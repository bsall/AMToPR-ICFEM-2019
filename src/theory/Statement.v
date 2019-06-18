Definition Effect { S : Type } := S -> S.

Definition Predicate { T : Type } := T -> Prop.

Definition Specification { T U : Type } := T -> U -> Prop.

Notation "T >> U" := (@Specification T U) (at level 0).


Inductive Stmt { T : Type } : Type := 
| Void 
| Assignment : @Effect T -> @Stmt T
| Seq : @Stmt T -> @Stmt T -> @Stmt T
| If : @Predicate T -> @Stmt T -> @Stmt T -> @Stmt T 
| While : @Predicate T -> @Stmt T -> @Stmt T 
| Spec : @Specification T T -> @Stmt T
| Block : @Stmt T -> @Stmt T -> @Stmt T.

Definition Skip { T : Type } := @Assignment T (fun s => s).

Fixpoint BlockFree { T : Type } (s : @Stmt T) :=
  match s with
  | Void => True
  | Assignment _ => True
  | Seq S1 S2 => BlockFree S1 /\ BlockFree S2
  | If _ S1 S2 => BlockFree S1 /\ BlockFree S2
  | While _ S1 => BlockFree S1
  | Spec _ => True
  | Block _ _ => False
  end.

Notation "' x := y" := (Assignment (fun x => y)) (at level 50, x pattern, format "' x  :=  y") : stmt_scope.
Notation "x ; y" := (Seq x y) (at level 51, format "'[v' x ; '/' y ']'", right associativity) : stmt_scope.
Notation "'IIf' c 'Then' p 'Else' q 'End'" :=
  (If c p q) (at level 52, format "'[v' IIf  c   Then '/'  p '/' Else '/'  q '/' End ']'") : stmt_scope.
Notation "'IIf' c 'Then' p 'End'" :=
  (If c p Skip) (at level 52, format "'[v' IIf  c  Then  p  End ']'") : stmt_scope.
Notation "'WWhile' c 'Do' p 'Done'" :=
  (While c p) (at level 52, format "'[v' WWhile  c  Do '/'  p '/' Done ']'") : stmt_scope.
Notation "⟨ x ⟩" := (Spec x) (at level 0, format "⟨ x ⟩") : stmt_scope.

Bind Scope stmt_scope with Stmt.