module

public import CatalanMeasure.GenD.Uniform.Bank540.Ledger.Gate

@[expose] public section

/-! Axiom audit for lane G5c (`Bank540/Ledger`). -/

open CatalanMeasure.GenD.Uniform.Bank540.Ledger

#print axioms ledger_growth
#print axioms partial_growth
#print axioms ledgerWins_cert
#print axioms ledgerWins_area
#print axioms frobLB
#print axioms seen_card
#print axioms H1_cell
#print axioms P1a_cell
#print axioms tail_cell
#print axioms A_cell
#print axioms frob_cell
#print axioms gate
#print axioms gate_of_remaining
