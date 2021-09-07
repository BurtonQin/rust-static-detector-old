use rustc_middle::mir::{Body, Location, Statement, Terminator};

#[derive(Debug, Clone, Copy)]
pub struct Instruction<'tcx> {
    pub body: &'tcx Body<'tcx>,
    pub location: Location,
}

impl<'tcx> Instruction<'tcx> {
    // location must correspond to body
    pub fn new_unchecked(body: &'tcx Body<'tcx>, location: Location) -> Self {
        Instruction { location, body }
    }

    pub fn new(body: &'tcx Body<'tcx>, location: Location) -> Option<Self> {
        if !Instruction::is_valid(body, location) {
            None
        } else {
            Some(Instruction { body, location })
        }
    }

    pub fn is_valid(body: &Body<'tcx>, location: Location) -> bool {
        let block = match body.basic_blocks().get(location.block) {
            Some(block) => block,
            None => return false,
        };
        location.statement_index <= block.statements.len()
    }

    #[inline]
    pub fn is_terminator(&self) -> bool {
        self.location.statement_index == self.body[self.location.block].statements.len()
    }

    /// # panic: if the location is not a statement
    pub fn get_statement(&self) -> &Statement<'tcx> {
        &self.body[self.location.block].statements[self.location.statement_index]
    }

    /// # panic: if the location is not a terminator
    pub fn get_terminator(&self) -> &Terminator<'tcx> {
        assert!(self.is_terminator());
        self.body[self.location.block].terminator()
    }

    pub fn predecessors(&self) -> Vec<Instruction<'tcx>> {
        let mut preds = Vec::new();
        if self.location.statement_index == 0 {
            for block in &self.body.predecessors()[self.location.block] {
                preds.push(Instruction {
                    body: self.body,
                    location: self.body.terminator_loc(*block),
                });
            }
        } else {
            let pred_loc = Location {
                block: self.location.block,
                statement_index: self.location.statement_index - 1,
            };
            preds.push(Instruction {
                body: self.body,
                location: pred_loc,
            });
        }
        preds
    }

    pub fn successors(&self) -> Vec<Instruction<'tcx>> {
        let mut succs = Vec::new();
        if self.is_terminator() {
            for block in self.body[self.location.block].terminator().successors() {
                succs.push(Instruction {
                    body: self.body,
                    location: Location {
                        block: *block,
                        statement_index: 0,
                    },
                });
            }
        } else {
            let succ_loc = Location {
                block: self.location.block,
                statement_index: self.location.statement_index + 1,
            };
            succs.push(Instruction {
                body: self.body,
                location: succ_loc,
            });
        }
        succs
    }
}
