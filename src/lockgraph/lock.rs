// #[derive(Debug, Hash, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub struct LockGuard {
    // def_id, substs, local
}

impl LockGuard {
    pub fn type_of(&self) -> LockGuardType { todo!{} }
    pub fn direct_src_of(&self) -> ! {}
    pub fn final_src_of(&self) -> ! {}
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LockGuardType {
    StdSync(StdSyncLockGuardType),
    ParkingLot(ParkingLotLockGuardType),
    LockApi(ParkingLotLockGuardType),  // lock_api is the same as parking_lot
    Spin(SpinLockGuardType),
    SpinPub(SpinLockGuardType),  // spin::RwLock is the same as spin::rw_lock::RwLock
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum StdSyncLockGuardType {
    MutexGuard,
    RwLockReadGuard,
    RwLockWriteGuard,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ParkingLotLockGuardType {
    MutexGuard,
    RwLockReadGuard,
    RwLockWriteGuard,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SpinLockGuardType {
    MutexGuard,
    RwLockReadGuard,
    RwLockWriteGuard,
}

impl LockGuardType {
    pub fn may_deadlock_with(&self, other: &Self) -> bool {
        if self.must_deadlock_with(self, other) {
            return true;
        }
        use LockGuardType::*;
        match (*self, *other) {
            (StdSync(StdSyncLockGuardType::RwLockReadGuard), StdSync(StdSyncLockGuardType::RwLockReadGuard)) => true,
            (ParkingLot(ParkingLotLockGuardType::RwLockReadGuard), ParkingLot(ParkingLotLockGuardType::RwLockReadGuard)) => true,
            (LockApi(ParkingLotLockGuardType::RwLockReadGuard), LockApi(ParkingLotLockGuardType::RwLockReadGuard)) => true,
            _ => false,
        }
    }

    pub fn must_deadlock_with(&self, other: &Self) -> bool {
        use LockGuardType::*;
        match (*self, *other) {
            (StdSync(StdSyncLockGuardType::MutexGuard), StdSync(StdSyncLockGuardType::MutexGuard)) => true,
            (StdSync(StdSyncLockGuardType::RwLockReadGuard), StdSync(StdSyncLockGuardType::RwLockWriteGuard)) => true,
            (StdSync(StdSyncLockGuardType::RwLockWriteGuard), StdSync(StdSyncLockGuardType::RwLockReadGuard(_))) => true,
            (StdSync(StdSyncLockGuardType::RwLockWriteGuard), StdSync(StdSyncLockGuardType::RwLockWriteGuard)) => true,
            (ParkingLot(ParkingLotLockGuardType::MutexGuard), ParkingLot(ParkingLotLockGuardType::MutexGuard)) => true,
            (ParkingLot(ParkingLotLockGuardType::RwLockReadGuard), ParkingLot(ParkingLotLockGuardType::RwLockWriteGuard)) => true,
            (ParkingLot(ParkingLotLockGuardType::RwLockWriteGuard), ParkingLot(ParkingLotLockGuardType::RwLockReadGuard)) => true,
            (ParkingLot(ParkingLotLockGuardType::RwLockWriteGuard), ParkingLot(ParkingLotLockGuardType::RwLockWriteGuard)) => true,
            (LockApi(ParkingLotLockGuardType::MutexGuard), LockApi(ParkingLotLockGuardType::MutexGuard)) => true,
            (LockApi(ParkingLotLockGuardType::RwLockReadGuard), LockApi(ParkingLotLockGuardType::RwLockWriteGuard)) => true,
            (LockApi(ParkingLotLockGuardType::RwLockWriteGuard), LockApi(ParkingLotLockGuardType::RwLockReadGuard)) => true,
            (Spin(SpinLockGuardType::MutexGuard), Spin(SpinLockGuardType::MutexGuard)) => true,
            (Spin(SpinLockGuardType::RwLockReadGuard), Spin(SpinLockGuardType::RwLockWriteGuard)) => true,
            (Spin(SpinLockGuardType::RwLockWriteGuard), Spin(SpinLockGuardType::RwLockReadGuard)) => true,
            (Spin(SpinLockGuardType::RwLockWriteGuard), Spin(SpinLockGuardType::RwLockWriteGuard)) => true,
            (SpinPub(SpinLockGuardType::MutexGuard), SpinPub(SpinLockGuardType::MutexGuard)) => true,
            (SpinPub(SpinLockGuardType::RwLockReadGuard), SpinPub(SpinLockGuardType::RwLockWriteGuard)) => true,
            (SpinPub(SpinLockGuardType::RwLockWriteGuard), SpinPub(SpinLockGuardType::RwLockReadGuard)) => true,
            (SpinPub(SpinLockGuardType::RwLockWriteGuard), SpinPub(SpinLockGuardType::RwLockWriteGuard)) => true,
            _ => false,
        }
    }
}

pub struct LockType {
}