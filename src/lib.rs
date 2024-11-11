pub fn add(left: u64, right: u64) -> u64 {
    left + right
}

trait WaterFallLock {
    fn new(num: usize) -> Self;
    fn size(&self) -> usize;
    fn get(&self, index: usize) -> u8;
    fn set(&self, index: usize, val: u8);

    fn reset(&mut self) {
        for i in 0..self.size() {
            self.set(i, 0);
        }
    }

    fn wait(&self, num: usize, val: u8) {
        while self.get(num) != val {}
    }
}

use crossbeam::atomic::AtomicCell;
use crossbeam_utils::CachePadded;

pub struct PaddedWaterFallLock<T>
where
    T: From<u8> + Into<u8> + Copy,
{
    wfc: Vec<CachePadded<AtomicCell<T>>>,
}

impl<T> WaterFallLock for PaddedWaterFallLock<T>
where
    T: From<u8> + Into<u8> + Copy,
{
    fn new(num: usize) -> Self {
        let mut wfc = Vec::<CachePadded<AtomicCell<T>>>::new();
        wfc.reserve(num);
        for _ in 0..num {
            wfc.push(CachePadded::new(AtomicCell::new(T::from(0u8))));
        }
        PaddedWaterFallLock { wfc }
    }

    fn size(&self) -> usize {
        self.wfc.len()
    }

    fn get(&self, index: usize) -> u8 {
        let padded_get_ref: &CachePadded<AtomicCell<T>> = unsafe { self.wfc.get_unchecked(index) };
        let get_ref: &AtomicCell<T> = &*padded_get_ref;
        let val: T = get_ref.load();
        val.into()
    }

    fn set(&self, index: usize, val: u8) {
        let padded_set_ref: &CachePadded<AtomicCell<T>> = unsafe { self.wfc.get_unchecked(index) };
        let set_ref: &AtomicCell<T> = &*padded_set_ref;
        set_ref.store(T::from(val));
    }
}

use vstd::prelude::*;
verus! {

use vstd::atomic::PAtomicUsize;
use vstd::atomic::PermissionUsize;
use vstd::prelude::Tracked;


pub struct VerifiedFallLock {
    wfc: Vec<CachePadded<PAtomicUsize>>,
    wfc_ghost: Tracked<GhostState>,
}

pub tracked struct GhostState {
    ghost length: int,
    tracked points_to_map: Map<int, PermissionUsize>,
}


impl VerifiedFallLock {

    pub closed spec fn view(&self) -> Seq<usize> {
        Seq::<usize>::new(
            self.ghost_state@.length as nat,
            |i: int| { self.ghost_state@.points_to_map[i].value() },
        )
    }

    spec fn well_formed_lock(&self, i: int) -> bool {
        &&& self.ghost_state@.points_to_map.dom().contains(i);
        &&& self.ghost_state@.points_to_map[i].is_for(self.wfc@[i].into_inner);
            && 0usize < self@[i] < u8::MAX;
    }

    pub closed spec fn well_formed(&self) -> bool {
        &&& self.ghost_state@.length >= 0
        &&& self.vec.size() == self.ghost_state@.length
        &&& (forall |i:int| 0 <= i && i < self.ghost_state@.length ==> self.ghost_state@.points_to_map.dom().contains(i))
        &&& (forall |i:int| 0 <= i && i < self.ghost_state@.length ==> self.well_formed_lock(i))
    }
}


impl WaterFallLock for VerifiedFallLock {
    fn new(num: usize) -> (s: Self)
        ensures
        s.well_formed(),
        s@.len() == 0,
    {
        let mut lock = VerifiedFallLock{
            wfc: Vec::new(),
            wfc_ghost: Tracked(GhostState {
                length: 0,
                points_to_map: Map::tracked_empty(),
        })};
        lock.wfc.reserve(num);
        for i in 0..num {
            let (atom, perm) = PAtomicUsize::new(0usize);
            lock.wfc.push(CachePadded::new(atom));
            proof {
                lock.wfc_ghost.borrow_mut().points_to_map.tracked_insert(i, perm);
                lock.wfc_ghost.borrow_mut().length += 1;
            }
        }
        lock
    }

    exec fn size(&self) -> usize {
        self.wfc.len()
    }

    exec fn get(&self, index: usize) -> u8 {
        let padded_get_ref: &CachePadded<PAtomicUsize> = unsafe { self.wfc.get_unchecked(index) };
        let get_ref: &PAtomicUsize = &*padded_get_ref;
        let val: usize = get_ref.load(Tracked(self.wfc_ghost[index]));
        val as u8
    }

    exec fn set(&self, index: usize, val: u8) {
        let padded_set_ref: &CachePadded<PAtomicUsize> = unsafe { self.wfc.get_unchecked(index) };
        let set_ref: &PAtomicUsize = &*padded_set_ref;
        let put_val = val as usize;
        set_ref.store(Tracked(self.wfc_ghost[index]), put_val);
    }


}

} // verus!
/*
pub struct PrefixSum<'a, A, B,
    transmute, scan_op, combiner, Conduit> {
    src: &'a mut [A],
    dst: &'a mut [B],
    paste: Conduit<B>,

};
*/
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let result = add(2, 2);
        assert_eq!(result, 4);
    }
}
