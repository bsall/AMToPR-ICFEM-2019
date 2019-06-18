Require Import ZArith.

Require Import Statement Wpr.

Require Import Lia.

Open Scope Z_scope.

Open Scope stmt_scope.

Definition spec : @Stmt (Z*Z) := ⟨fun '(x,y) '(x',y') => x' = y /\ y' = x⟩.

Definition prog :=
  '(x,y) := (x - y, y);
  '(x,y) := (x, x + y);
  '(x,y) := (y - x, y).

Theorem correctness : prog ⊑ spec.
Proof. intros (x,y) _; simpl in *. lia. Qed.

Definition prog' :=
  '(x,y) := (x + y, y);
  '(x,y) := (x, x - y);
  '(x,y) := (x - y, y).

Theorem correctness'' : prog ⊑ prog'.
Proof. intros (x,y) _; simpl in *.
       f_equal; lia.
Qed.

Theorem correctness' : prog' ⊑ spec.
Proof. intros (x,y) _; simpl in *. lia. Qed.


Theorem prog_prog' : prog ⊑ prog' /\ prog' ⊑ prog.
Proof.
  split; intros (x,y) _; simpl in *; f_equal.
  all : lia.
Qed.

(* Polymorphic version *)

Definition poly_spec (T : Type) : @Stmt (T*T*T) := ⟨fun '(x,y,t) '(x',y',t') => x' = y /\ y' = x⟩.

Definition poly_prog (T : Type) : @Stmt (T * T * T) :=
  '(x,y,t) := (x,y,x);
  '(x,y,t) := (y,y,t);
  '(x,y,t) := (x,t,t).

Theorem poly_correctness : forall T, poly_prog T ⊑ poly_spec T.
Proof. intros T ((x,y),t) _; simpl in *. auto. Qed.

Close Scope stmt_scope.