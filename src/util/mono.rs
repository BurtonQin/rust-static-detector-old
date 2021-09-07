use rustc_middle::ty::{self, Instance, TyCtxt, TypeFoldable};
/// Monomorphize a type T.
/// Inspired by rustc_mir::monomorphize::collector::MirNeighborCollector#monomorphize.
pub struct Monomorphizer<'tcx> {
    instance: Instance<'tcx>,
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> Monomorphizer<'tcx> {
    pub fn new(instance: Instance<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
        Self { instance, tcx }
    }

    pub fn monomorphize<T>(&self, value: T) -> T
    where
        T: TypeFoldable<'tcx>,
    {
        self.instance.subst_mir_and_normalize_erasing_regions(
            self.tcx,
            ty::ParamEnv::reveal_all(),
            value,
        )
    }
}
