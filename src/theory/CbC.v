Require Import Statement ThreadedPredicative Wpr.

Open Scope stmt_scope.

Reserved Notation "'φ' d" (at level 70, no associativity).
Reserved Notation "'φa' d" (at level 70, no associativity).
Reserved Notation "'φc' d" (at level 70, no associativity).

Fixpoint dsem { T } (d : @Stmt T) :=
  match d with
  | Statement.Void => (Statement.Void,Statement.Void)
  | Statement.Assignment f => (Statement.Assignment f,Statement.Assignment f)
  | Statement.Spec s => (Statement.Spec s,Statement.Spec s)
  | Statement.Seq d1 d2 => ((φa d1);(φa d2), (φc d1);(φc d2))
  | Statement.If p d1 d2 => (IIf p Then (φa d1) Else (φa d2) End, IIf p Then (φc d1) Else (φc d2) End)
  | Statement.While p d => (IIf p Then ⟨fun s s' => pred (φa d) s s' /\ ~ p s'⟩ End, WWhile p Do (φc d) Done)
  | Statement.Block s d => (s,φc d)
  end
where "'φ' d" := (dsem d) and "'φa' d" := (fst (dsem d)) and "'φc' d" := (snd (dsem d)).

(* Correct by Construction predicate *)
Inductive Design { T } : @Stmt T -> Prop :=
  | Void : Design Void
  | Spec : forall s, Design (Spec s)
  | Assignment : forall f, Design (Assignment f)
  | Seq : forall d1 d2, Design d1 -> Design d2 -> Design (Seq d1 d2)
  | If : forall p d1 d2, Design d1 -> Design d2 -> Design (If p d1 d2)
  | While :
      forall p d,
        Design d
        -> (well_founded (fun s s' => p s' /\ pred (φa d) s' s /\ p s)
           /\ (forall s s', p s /\ pred (φa d) s s' -> (forall sx, (p s' /\ pred (φa d) s' sx \/ ~ p s' /\ s' = sx) -> p s /\ pred (φa d) s sx)
                                               /\ exists sx, p s' /\ pred (φa d) s' sx \/ ~ p s' /\ s' = sx))
          -> Design (While p d)
  | Block : forall s d, Design d -> (φa d) ⊑ s -> Design (Block s d).

Theorem soundness : forall {T} {d : @Stmt T}, Design d -> (φc d) ⊑ (φa d).
Proof.
  intros T A HHd.
  induction HHd.
  { firstorder. }
  { apply refines_reflexive. }
  { apply refines_reflexive. }
  { simpl (dsem _).
    destruct (dsem d1).
    destruct (dsem d2).
    apply (Seq_monotonic_refines _ _ _ _ _ IHHHd1 IHHHd2).
  }
  { simpl (dsem _).
    destruct (dsem d1).
    destruct (dsem d2).
    apply (If_monotonic_refines _ _ _ _ _ _ IHHHd1 IHHHd2).
  }
  { apply (refines_trans _ _ (WWhile p Do (φa d) Done)).
    { simpl (dsem _).
      destruct (dsem d).
      inversion H; subst.
      simpl in *. 
      apply (While_monotonic_refines _ _ _ _ IHHHd).
    }
    { destruct H as [H0 H1].
      simpl (dsem _).
      destruct (dsem d); simpl in *.
      apply (wfd_while_refines_if' _ _ H0).
       intros.
       split.
       { apply (H1 _ _ H). }
       { apply (H1 _ _ H). }
     }
  }
  { simpl (dsem _).
    destruct (dsem d); simpl in *.
    apply (refines_trans _ _ _ _ IHHHd H).
  }
Qed.

Theorem completeness : forall T (P Q : @Statement.Stmt T), P ⊑ Q -> exists (d : @Stmt T), (φ (Statement.Block Q P)) = (φ d) /\ Design d.
Proof.
  intros T P.
  induction P; intros.
  { exists (Statement.Block Q Statement.Void); simpl.
    split; auto.
    apply (Block _ _ Void); simpl; auto.
  }
  { exists (Statement.Block Q (Statement.Assignment e)); simpl.
    split; auto.
    apply (Block _ _ (Assignment e)); simpl; auto.
  }
  { destruct (IHP1 _ (refines_reflexive _ _)) as (d1,(HHEq1,HHcbc1)).
    destruct (IHP2 _ (refines_reflexive _ _)) as (d2,(HHEq2,HHcbc2)).
    exists (Statement.Block Q (Statement.Seq d1 d2)); simpl.
    rewrite <- HHEq1, <- HHEq2; simpl.
    split; auto.
    apply (Block _ _ (Seq d1 d2 HHcbc1 HHcbc2)).
    simpl; rewrite <- HHEq1, <- HHEq2.
    auto.
  }
  { destruct (IHP1 _ (refines_reflexive _ _)) as (d1,(HHEq1,HHcbc1)).
    destruct (IHP2 _ (refines_reflexive _ _)) as (d2,(HHEq2,HHcbc2)).
    exists (Statement.Block Q (Statement.If p d1 d2)); simpl.
    rewrite <- HHEq1, <- HHEq2; simpl.
    split; auto.
    apply (Block _ _ (If p d1 d2 HHcbc1 HHcbc2)).
    simpl; rewrite <- HHEq1, <- HHEq2.
    auto.
  }
  { pose proof H as H'.
    rewrite while_rule_sound_and_complete in H'.
    destruct H' as (K,(HHpk,HHk)).
    destruct (IHP _ HHpk) as (d,(HHEq,HHcbc)).
    exists (Statement.Block Q (Statement.While p d)).
    split.
    { simpl.
      destruct (dsem d).
      inversion HHEq; subst.
      auto.
    }
    { unshelve eapply (Block _ _ (While p d HHcbc _)).
      { destruct HHk as (HHk,(HHk1,HHk2)).
        rewrite <- HHEq in *; simpl in *.
        split; auto.
        intros.
        pose proof (HHk1 _ (ex_intro _ _ H0)).
        simpl in *.
        unfold wpr_spec in *.
        clear -H0 H1.
        destruct H1.
        pose proof (H _ H0).
        clear -H2; auto.
      }
      { simpl.
        inversion HHEq; subst.
        simpl.
        apply HHk.
      }
    }
  }
  { exists (Statement.Block Q (Statement.Spec s)); simpl.
    split; auto.
    apply (Block _ _ (Spec s)); simpl.
    auto.
  }
  { assert (P2 ⊑ Q).
    { firstorder. }
    pose proof (IHP2 _ H0) as (d,HHd).
    exists d; simpl in *.
    auto.
  }
Qed.

Close Scope stmt_scope.

Definition CbCSpec { T } { D : @Stmt T } ( _ : Design D) := φa D.
Definition CbCImpl { T } { D : @Stmt T } ( _ : Design D) := φc D.
Notation "'Πa' D" := (CbCSpec D) (at level 70) : cbc_scope.
Notation "'Πc' D" := (CbCImpl D) (at level 70) : cbc_scope.


Notation "'Fail'" := Void (at level 89) : cbc_scope.
Notation "'Skip'" := (Assignment (fun s => s)) (at level 89) : cbc_scope.
Notation "' x ::= e" := (Assignment (fun x => e)) (at level 50, x pattern, format "' x  ::=  e") : cbc_scope.
Notation "⟨ spec ⟩" := (Spec spec) (at level 0) : cbc_scope.
Notation "'If' p 'Then' ct 'Else' cf 'End'" :=
  (If p _ _ ct cf) (at level 90,  format "'[v' If  p   Then '/'  ct '/' Else '/'  cf '/' End ']'") : cbc_scope.
Notation "stmt :{ impl }" := (Block stmt _ impl _) (at level 50) : cbc_scope.
Notation "'While' p 'Do' c 'Done'" := (While p _ c _) (at level 50, format "'[v' While  p  Do '/'  c '/' Done ']'") : cbc_scope.
Notation "d1 ;; d2" := (Seq _ _ d1 d2) (at level 51, right associativity) : cbc_scope.

Open Scope cbc_scope.

Notation "'If' p 'Then' ct 'End'" := (If p Then ct Else Skip End)
                                       (at level 90,  format "'[v' If p  Then '/' ct '/' End ']'") : cbc_scope.

Close Scope cbc_scope.

Bind Scope cbc_scope with Design.
