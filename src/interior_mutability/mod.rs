use rustc_middle::{
    mir::{visit::Visitor, Body, CastKind, Location, Operand, Rvalue, Statement, StatementKind},
    ty::TyCtxt,
};

pub struct InteriorMutabilityFinder<'tcx> {
    pub body: &'tcx Body<'tcx>,
    pub tcx: TyCtxt<'tcx>,
}

impl<'tcx> Visitor<'tcx> for InteriorMutabilityFinder<'tcx> {
    fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, location: Location) {
        if let Rvalue::Cast(CastKind::Misc, Operand::Move(place), ty) = rvalue {
            if ty.is_mutable_ptr() && ty.is_unsafe_ptr() {
                let place_ty = place.ty(self.body, self.tcx).ty;
                if !place_ty.is_mutable_ptr() && place_ty.is_unsafe_ptr() {
                    println!(
                        "{:?}:\n\t{:?}\n\t{:?}",
                        self.body.source.def_id(),
                        self.body[location.block].statements[location.statement_index],
                        self.body.source_info(location)
                    );
                }
            }
        }
    }
}
