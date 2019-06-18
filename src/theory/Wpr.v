Require Import DemonicComposition Statement LeastFixpoint Predicative.

Open Scope stmt_scope.

Definition wpr_spec { T : Type } (C S : T >> T) : T >> T := fun s s' => (forall sx, C s' sx -> S s sx) /\ (exists sx, C s' sx).

Lemma ll : forall T (P : T >> T), ⟨wpr_spec P P⟩;⟨wpr_spec P P⟩ ⊑ ⟨wpr_spec P P⟩.
Proof. firstorder. Qed.

Theorem wpr_spec_sseq :  forall T (C1 C2 S : T >> T) s s', wpr_spec (C1 ⊟ C2) S s s' <-> wpr_spec C1 (wpr_spec C2 S) s s'.
Proof. firstorder. Qed.

Theorem wpr_spec_and :  forall T (C S1 S2 : T >> T) s s',
    wpr_spec C (fun s s' => S1 s s' /\ S2 s s') s s' <-> wpr_spec C S1 s s' /\  wpr_spec C S2 s s'.
Proof. firstorder. Qed.

Theorem wpr_false : forall T (C : T >> T), forall s s', wpr_spec C (fun s s' => False) s s' <-> False.
Proof. firstorder. Qed.

Definition wpr_while { T : Type } C (K : T >> T -> T >> T) (S : T >> T) :=
   fun s s' => forall (X: Specification), (forall s s', (C s' /\ K X s s'  \/  ~ C s' /\ S s s') -> X s s') -> X s s'.

Fixpoint wpr { T : Type } (C : @Stmt T) (S : T >> T) : T >> T :=
  match C with
  | Statement.Void => fun s s' => False
  | Statement.Assignment effect => fun s s' => S s (effect s')
  | Statement.Seq C1 C2 => wpr C1 (wpr C2 S)
  | Statement.If p Ct Cf => fun s s' => (p s' /\ wpr Ct S s s') \/ (~ p s' /\ wpr Cf S s s')
  | Statement.While p C => wpr_while p (wpr C) S
  (*fun s s' => forall (T : Specification), (forall s s', (p s' /\ wpr C T s s'  \/  ~ p s' /\ S s s') -> T s s') -> T s s'*)
  | Statement.Spec spec => wpr_spec spec S
  | Statement.Block bspec bimpl => wpr bimpl S
  end.

Lemma wpr_monotonic_right : forall T C (S1 S2 : T >> T), (forall s s', S1 s s' -> S2 s s') -> forall s s', wpr C S1 s s' -> wpr C S2 s s'.
Proof. induction C; simpl in *; firstorder. Qed.

Definition wpr_while_functional { T : Type } C (P : @Stmt T) S X s s' := C s' /\ wpr P X s s'  \/  ~ C s' /\ S s s'.


Lemma wpr_while_functional_monotonic :
  forall T C (P : @Stmt T) (S T1 T2 : Specification),
    (forall s s', T1 s s' -> T2 s s') -> (forall s s', wpr_while_functional C P S T1 s s' -> wpr_while_functional C P S T2 s s').
Proof.
  intros T C P S T1 T2 HHT s s' [ (HHp,HHwpr) | HHwpr ].
  { left; split; auto; apply (wpr_monotonic_right _ _ _ _ HHT _ _ HHwpr). }
  { right; auto. }
Qed.

Theorem wpr_while_construct :
  forall T C (P : @Stmt T) S s s',  C s' /\ wpr P (wpr (Statement.While C P) S) s s' \/ ~ C s' /\ S s s' -> wpr (Statement.While C P) S s s'.
Proof.
  intros T C P S.
  apply (f_lfp_lfp (wpr_while_functional _ _ _) (wpr_while_functional_monotonic _ _ _ _)).
Qed.

Theorem wpr_while_destruct :
  forall T C (P : @Stmt T) S s s', wpr (Statement.While C P) S s s' -> C s' /\ wpr P (wpr (Statement.While C P) S) s s' \/ ~ C s' /\ S s s' .
Proof.
  intros T C P S.
  apply (lfp_f_lfp (wpr_while_functional _ _ _) (wpr_while_functional_monotonic _ _ _ _)).
Qed.

Theorem wpr_while_ind :
  forall T C (P : @Stmt T) S X,
    (forall s s',  C s' /\ wpr P X s s'  \/  ~ C s' /\ S s s' -> X s s')
    -> forall s s', wpr (Statement.While C P) S s s' -> X s s'.
Proof.
  intros *.
  apply (f_lfp  (wpr_while_functional _ _ _)).
Qed.

Lemma right_extensionality :
  forall T (C S1 S2 : T >> T), (forall s s', S1 s s' -> S2 s s') -> forall s s', wpr (Statement.Spec C) S1 s s' -> wpr (Statement.Spec C) S2 s s'.
Proof. firstorder. Qed.

Lemma left_extensionality :
  forall T (C1 C2 S : T >> T),
    (forall s s', C1 s s' <-> C2 s s') -> forall s s', wpr (Statement.Spec C2) S s s' <-> wpr (Statement.Spec C1) S s s'.
Proof. firstorder. Qed.

Lemma wpr_pred : forall T (C : @Stmt T) S s s', wpr (Statement.Spec (pred C)) S s s' <-> wpr C S s s'.
Proof.
  induction C.
  { firstorder. }
  { simpl; intros S s s'; split.
    { intros (HHspec,_); apply HHspec; reflexivity. }
    { intros HHspec; split; eauto.
      intros sx HHeq; subst sx. exact HHspec.
    }
  }
  { simpl; intros S s s'; split.
    { intros HHpred.
      apply (IHC1); auto.
      apply (right_extensionality _ _ (wpr (Statement.Spec (pred C2)) S)).
      { intros r r'; apply IHC2; auto. }
      { firstorder. }
    }
    { intros HHwpr.
      apply IHC1 in HHwpr; auto. apply (right_extensionality _ _ _ (wpr (Statement.Spec (pred C2)) S)) in HHwpr.
      { simpl in HHwpr; firstorder. }
      { intros r r'; apply (IHC2 _ _ _); auto. }
    } 
  }
  { simpl; intros S s s'.
    split.
    { intros [HHpred1 [sx [(HHp,HHpred2) | (HHp,HHpred2)]]].
      { left; split; auto; apply IHC1; firstorder. }
      { right; split; auto; apply IHC2; firstorder. }
    }
    { intros [(HHp,HHwpr) | (HHp,HHwpr)].
      { apply IHC1 in HHwpr; firstorder. }
      { apply IHC2 in HHwpr; firstorder. }
    }
  }
  { intros S s s'.
    split.
    { generalize s; clear s.
      pattern s'; apply (well_founded_ind (while_well_founded p (pred C))).
      clear s'.
      intros s' HHwfdind s HHwpr.
      destruct HHwpr as (H1,H2).
      destruct H2 as (sx,H2); simpl in H2.
      pose proof H2 as H2'.
      apply while_destruct in H2. 
      destruct H2 as [ (HHps',((sy,(HH11,HH12)),HH2)) | (HHps',HH) ].
      { apply wpr_while_construct; left; split; auto.
        apply IHC; auto; split; eauto.
        intros sz HHpred.
        apply HHwfdind.
        { repeat split; auto.
          exists sx; apply while_construct; left; split; auto.
          split; eauto.
        }
        { simpl; split; eauto.
          intros sz' HHpred'.
          apply H1; simpl.
          apply while_construct; left; split; auto.
          split; eauto.
        }
      }
      { apply wpr_while_construct; right; split; auto.
        apply H1; apply while_construct; subst sx; auto.
      }
    }
    { apply (wpr_while_ind _ _ _ _ _); clear s s'.
      Transparent wpr.
      intros r r' [[HHp HHwpr] | [HHp HHwpr] ].
      { apply IHC in HHwpr; auto.
        destruct HHwpr as [HH1 (sx,HH2)].
        split.
        { intros sy HHpred; simpl in HHpred.
          pose proof HHpred as HHpred'.
          apply while_destruct in HHpred'.
          destruct HHpred' as [ (_,((sx',(HH31,HH32)),HH4)) | (HHp1,_) ]; try contradiction.
          apply (HH1 _ HH31).
          auto.
        }
        { destruct (HH1 _ HH2) as (HH3,(sx',HH4)).
          exists sx'; simpl; apply while_construct. left ; split; auto.
          split; eauto.
          intros sy HHpred.
          destruct (HH1 _ HHpred); eauto.
        }
      }
      { simpl; split.
        { intros sx HHwhile.
          apply while_destruct in HHwhile.
          destruct HHwhile as [ (HHpr',(HH1,HH2)) | (_,HHeq) ]; try contradiction.
          subst sx; exact HHwpr.
        }
        { exists r'; apply while_construct; right; auto. }
      }
    } 
  }
  { reflexivity. }
  { intros; simpl.
    apply IHC2.
  }
Qed.

Lemma wpr_seq : forall T (C :@Stmt T) S, forall s sx, wpr C S s sx <-> ((forall s', pred C sx s' -> S s s') /\ exists s', pred C sx s').
Proof.
  intros T C S s sx.
  split.
  { intros HHwpr.
    apply wpr_pred in HHwpr; auto.
  }
  { intros HHpred.
    apply wpr_pred; auto.
  }
Qed.

Theorem wpr_refines : forall T (C : @Stmt T) S, (forall s, (exists s', (pred S) s s') -> wpr C (pred S) s s) <-> refines C S.
Proof.
  intros. unfold refines; intros; split.
  { intros HHwpr s HHex; apply (wpr_seq _ C (pred S) s s); auto. }
  { intros HHpred s HHex; apply (wpr_seq _ C (pred S) s s); auto. }
Qed.

Close Scope stmt_scope.

Require Import ThreadedPredicative.

Open Scope stmt_scope.

Definition refines { T : Type } (P Q : @Stmt T) :=
  (forall s, (exists s', (ThreadedPredicative.pred Q) s s') -> wpr P (ThreadedPredicative.pred Q) s s).


Theorem refines_predicative_refines : forall T (P Q : @Stmt T), refines P Q <-> Predicative.refines P Q.
Proof.
  intros T P Q.
  rewrite <- (wpr_refines _ _ _).
  unfold refines.
  split.
  { intros HHrefines s (s',HHq).
    rewrite <- (wpr_pred _ _ _ _ _).
    apply (right_extensionality _ (Predicative.pred P) (ThreadedPredicative.pred Q) (Predicative.pred Q)).
    { apply pred_old_pred. }
    { rewrite (wpr_pred _ _ _ _ _).
      apply HHrefines.
      exists s'; apply pred_old_pred; exact HHq.
    }
  }
  { intros HHrefines s (s',HHq).
    rewrite <- (wpr_pred _ _ _ _ _).
    apply (right_extensionality _ (Predicative.pred P) (Predicative.pred Q) (ThreadedPredicative.pred Q)).
    { apply pred_old_pred. }
    { rewrite (wpr_pred _ _ _ _ _).
      apply HHrefines.
      exists s'; apply pred_old_pred; exact HHq.
    }
  }
Qed.

Notation "C1 ⊑ C2" := (refines C1 C2) (at level 60, format "C1  ⊑  C2").

Theorem refines_reflexive : forall (T : Type)  (P : @Stmt T), refines P P.
Proof.
  intros T P.
  rewrite (refines_predicative_refines _ _ _).
  apply (Predicative.refines_reflexive _ P).
Qed.

Theorem refines_trans : forall (S : Type)  (P Q R : @Stmt S), refines P Q -> refines Q R -> refines P R.
Proof.
  intros S P Q R.
  repeat rewrite refines_predicative_refines.
  repeat rewrite refines_old_refines.
  apply refines_trans.
Qed.

Theorem Seq_left_monotonic_refines :
  forall (S : Type) (P1 P2 Q : @Stmt S), refines P1 P2 -> refines (Seq P1 Q) (Seq P2 Q).
Proof.
  intros S P1 P2 Q.
  repeat rewrite refines_predicative_refines.
  repeat rewrite refines_old_refines.
  apply Seq_left_monotonic_refines.
Qed.

Theorem Seq_right_monotonic_refines :
  forall (S : Type) (P Q1 Q2 : @Stmt S), refines Q1 Q2 -> refines (Seq P Q1) (Seq P Q2).
Proof.
  intros S P Q1 Q2.
  repeat rewrite refines_predicative_refines.
  repeat rewrite refines_old_refines.
  apply Seq_right_monotonic_refines.
Qed.

Theorem Seq_monotonic_refines :
  forall (S : Type) (P1 P2 Q1 Q2 : @Stmt S),
    refines P1 Q1
    -> refines P2 Q2
    -> refines (Seq P1 P2) (Seq Q1 Q2).
Proof.
  intros S P1 P2 Q1 Q2.
  repeat rewrite refines_predicative_refines.
  repeat rewrite refines_old_refines.
  apply Seq_monotonic_refines.
Qed.

Theorem If_monotonic_refines :
  forall (S : Type) C (Pt Qt Pf Qf : @Stmt S),
    refines Pt Qt
    -> refines Pf Qf
    -> refines (If C Pt Pf) (If C Qt Qf).
Proof.
  intros S C Pt Pf Qt Qf.
  repeat rewrite refines_predicative_refines.
  repeat rewrite refines_old_refines.
  apply If_monotonic_refines.
Qed.

Theorem While_monotonic_refines :
  forall (S : Type) C (P Q : @Stmt S),
    refines P Q
    -> refines (While C P) (While C Q).
Proof.
  intros S C P Q.
  repeat rewrite refines_predicative_refines.
  repeat rewrite refines_old_refines.
  apply While_monotonic_refines.
Qed.

Theorem refines_extensionality_left : forall T (P1 P2 Q : @Stmt T), (forall s s', (pred P1) s s' <-> (pred P2) s s') -> refines P1 Q <-> refines P2 Q.
Proof.
  intros T P1 P2 Q.
  repeat rewrite refines_predicative_refines.
  repeat rewrite refines_old_refines.
  apply refines_extensionality_left.
Qed.


Theorem wfd_while_iff_if : forall { S : Type } C (P : @Stmt S),
    well_founded (fun s s' => C s' /\ pred P s' s /\ C s)
    -> (⟨fun s s' => C s /\ pred P s s'⟩;⟨fun s s' => C s /\ pred P s s' \/ ~ C s /\ s = s'⟩) ⊑ ⟨fun s s' => C s /\ pred P s s'⟩
    -> forall s s', while C P s s' <-> pred (IIf C Then P End) s s' /\ ~ C s'.
Proof.
  intros S C P HHwfd HHrefines s s'.
  rewrite refines_predicative_refines in HHrefines.
  apply ThreadedPredicative.wfd_while_iff_if; auto.
Qed.

Theorem wfd_while_refines_if : forall { S : Type } C (P : @Stmt S),
    well_founded (fun s s' => C s' /\ pred P s' s /\ C s)
    -> (⟨fun s s' => C s /\ pred P s s'⟩;⟨fun s s' => C s /\ pred P s s' \/ ~ C s /\ s = s'⟩) ⊑ ⟨fun s s' => C s /\ pred P s s'⟩
    -> WWhile C Do P Done ⊑ IIf C Then ⟨fun s s' => pred P s s' /\ ~ C s'⟩ End.
Proof.
  intros *.
  repeat rewrite refines_predicative_refines.
  repeat rewrite refines_old_refines.
  apply ThreadedPredicative.wfd_while_refines_if.
Qed.

Theorem if_refines_wfd_while : forall { S : Type } C (P : @Stmt S),
    well_founded (fun s s' => C s' /\ pred P s' s /\ C s)
    -> (⟨fun s s' => C s /\ pred P s s'⟩;⟨fun s s' => C s /\ pred P s s' \/ ~ C s /\ s = s'⟩) ⊑ ⟨fun s s' => C s /\ pred P s s'⟩
    -> IIf C Then ⟨fun s s' => pred P s s' /\ ~ C s'⟩ End ⊑ WWhile C Do P Done.
Proof.
  intros *.
  repeat rewrite refines_predicative_refines.
  repeat rewrite refines_old_refines.
  apply if_refines_wfd_while.
Qed. 

Theorem wfd_while_iff_if' : forall { S : Type } C (P : @Stmt S),
    well_founded (fun s s' => C s' /\ pred P s' s /\ C s)
    -> (forall s s', C s /\ pred P s s' ->
               (forall sx, (C s' /\ pred P s' sx \/ ~ C s' /\ s' = sx) -> C s /\ pred P s sx)
               /\ exists sx, C s' /\ pred P s' sx \/ ~ C s' /\ s' = sx)
    -> forall s s', while C P s s' <-> pred (IIf C Then P End) s s' /\ ~ C s'.
Proof.
  intros S C P HHwfd HHrefines s s'.
  apply ThreadedPredicative.wfd_while_iff_if'; auto.
Qed.

Theorem wfd_while_refines_if' : forall { S : Type } C (P : @Stmt S),
    well_founded (fun s s' => C s' /\ pred P s' s /\ C s)
    -> (forall s s', C s /\ pred P s s' ->
               (forall sx, (C s' /\ pred P s' sx \/ ~ C s' /\ s' = sx) -> C s /\ pred P s sx)
               /\ exists sx, C s' /\ pred P s' sx \/ ~ C s' /\ s' = sx)
    -> WWhile C Do P Done ⊑ IIf C Then ⟨fun s s' => pred P s s' /\ ~ C s'⟩ End.
Proof.
  intros *.
  repeat rewrite refines_predicative_refines.
  repeat rewrite refines_old_refines.
  apply ThreadedPredicative.wfd_while_refines_if'.
Qed.

Theorem while_rule_sound_and_complete : forall { T : Type } (C : @Predicate T) P R,
    WWhile C Do P Done ⊑ R
    <-> exists K, P ⊑ K
           /\ well_founded (fun s s' => C s' /\ pred K s' s /\ C s)
           /\ (⟨fun s s' => C s /\ pred K s s'⟩;⟨fun s s' => C s /\ pred K s s' \/ ~ C s /\ s = s'⟩) ⊑ ⟨fun s s' => C s /\ pred K s s'⟩
           /\ IIf C Then ⟨fun s s' => pred K s s' /\ ~ C s'⟩ End ⊑ R.
Proof.
  intros *.
  repeat setoid_rewrite refines_predicative_refines.
  repeat setoid_rewrite refines_old_refines.
  apply ThreadedPredicative.while_rule_sound_and_complete.
Qed.

Lemma wpr_and : forall { T } (C : @Predicate T) P (K1 K2 : T >> T) s s',
    wpr P (fun s s' => K1 s s' /\ K2 s s') s s' <-> wpr P K1 s s' /\ wpr P K2 s s'.
Proof.
  setoid_rewrite <- wpr_pred; simpl.
  setoid_rewrite wpr_spec_and.
  reflexivity.
Qed.

Close Scope stmt_scope.