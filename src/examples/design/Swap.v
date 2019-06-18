Require Import ZArith Lia.

Require Import Statement.

Require Import Wpr CbC.

Open Scope cbc_scope.

Program Definition Swap :=
  ⟨ fun '(x,y) '(x',y')  => x' = y /\ y' = x ⟩
  :{ '(x,y) := (y,x) :{
       '(x,y) ::= (x+y, y);;
       '(x,y) ::= (x, x-y);;
       '(x,y) ::= (x-y, y)
     }                 
   }.

Next Obligation.
  intros (x,y) _; simpl; f_equal.
  all: lia.
Qed.

Next Obligation.
  intros (x,y) _; simpl.
  auto.
Qed.

Theorem proof : (Πc Swap) ⊑ (Πa Swap).
Proof. apply (CbC.soundness Swap). Qed.

Check proof.
Print Assumptions proof.

Close Scope cbc_scope.
