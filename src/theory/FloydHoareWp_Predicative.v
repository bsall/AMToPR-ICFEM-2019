Require Import Statement FloydHoareWp Predicative.

Lemma pred_if_hoare :
  forall (T : Type) (C : @Stmt T) P Q, BlockFree C -> ValidHoareTriple P C Q -> ValidHoareTriple P (Statement.Spec (pred C)) Q.
Proof.
  induction C as [ | | | | | | ]; intros P Q BFC; simpl.
  { intros HHtriple; inversion_clear HHtriple; constructor; firstorder. }
  { intros HHtriple; inversion_clear HHtriple; constructor.
    intros s HHp.
    split.
    { intros s' HHeq; subst s'; auto. }
    { eauto. }
  }
  {  intros HHtriple; inversion_clear HHtriple; inversion BFC as [BFC1 BFC2]; clear BFC.
    apply (IHC1 _ _) in H; auto; apply (IHC2 _ _) in H0; auto; inversion_clear H; inversion_clear H0; constructor.
    intros s HHp; split.
    { firstorder. }
    { destruct (H1 _ HHp) as (HH1,(s',HH2)).
      destruct (H _ (HH1 _ HH2)) as (HH3,(s'',HH4)).
      exists s''; firstorder.
    }
  }
  { intros HHtriple; inversion_clear HHtriple; inversion BFC as [BFC1 BFC2]; clear BFC.
    constructor.
    intros s HHp; split.
    { intros s' [HHpred | HHpred].
      { apply (IHC1 _ _) in H0; auto; inversion_clear H0; firstorder. }
      { apply (IHC2 _ _) in H1; auto; inversion_clear H1; firstorder. }
    }
    { apply (IHC1 _ _) in H0; auto; inversion_clear H0; apply (IHC2 _ _) in H1; auto; inversion_clear H1.
      destruct (H _ HHp) as [HHpt | HHpf].
      { destruct (H2 _ (conj HHpt HHp)) as (_,(s',HHpred)); eauto. }
      { destruct (H0 _ (conj HHpf HHp)) as (_,(s',HHpred)); eauto. }
    }
  }
  { intros HHtriple; inversion_clear HHtriple; simpl in BFC.
    constructor; intros s HHp; split.
    { intros s' HHwhile. apply H3.
      { apply (while_end _ _ _ _ _ HHwhile).  }
      { generalize (H1 _ HHp).
        pattern s,s'; apply (while_ind _ _ _ _ _ HHwhile).
        intros r r'; simpl; intros [(HHwhile1,((sx,(HHpsx,HHwhile21)),HHwhile22)) | (HHp1,HHeq)].
        { pose proof (H2 (V r)) as HHtriple1.
          apply (IHC _ _) in HHtriple1; auto.
          inversion_clear HHtriple1.
          intros; apply HHwhile21; auto.
          apply (H4 r); auto.
        }
        { subst r'; auto. }
      }
    }
    { destruct (H _ (H1 _ HHp)).
      { assert (well_founded (fun s s' => R (V s) (V s'))).
        { constructor.
          pattern (V a); apply (well_founded_ind H0); eauto; intros.
          constructor; intros.
          apply (H5 _ H6); auto.
        }
        { generalize H4 (H1 _ HHp).
          pattern s; apply (well_founded_ind H5).
          intros.
          pose proof (H2 (V x)).
          apply (IHC _ _) in H9; auto.
          inversion_clear H9.
          destruct (H10 _ (conj H7 (conj H8 (eq_refl _)))).
          destruct H11 as (s',H11).
          destruct (H9 _ H11).
          destruct (H _ H12).
          { destruct (H6 _ H13 H14 H12) as (s'',H15).
            exists s''.
            apply while_construct; left; split; auto; split; eauto.
            intros sx HHpred.
            destruct (H9 _ HHpred).
            destruct (H _ H16).
            { apply H6; auto. }
            { exists sx; apply while_construct; right; auto. }
          }
          { exists s'; apply while_construct; left; split; auto; split.
            { exists s'; split; auto; apply while_construct; right; auto. }
            { intros sx HHpred.
              destruct (H9 _ HHpred).
              destruct (H _ H15).
              { apply H6; auto. }
              { exists sx; apply while_construct; right; auto. }
            }
          }
        }
      }
      { exists s; apply while_construct; right; auto. }
    }
  }
  { auto. }
  { simpl in BFC; contradiction. } 
Qed.

Lemma hoare_if_pred :
  forall (S : Type) (C : @Stmt S) P Q, BlockFree C -> ValidHoareTriple P (Statement.Spec (pred C)) Q -> ValidHoareTriple P C Q.
Proof.
  induction C as [ | | | | | | ]; intros P Q BFC; simpl.
  { intros HHtriple; inversion_clear HHtriple; constructor; firstorder. }
  { intros HHtriple; inversion_clear HHtriple; constructor.
    firstorder.
  }
  { intros HHtriple; inversion_clear HHtriple; inversion BFC as [BFC1 BFC2]; clear BFC.
    apply (Seq _ (fun s => (forall sx, (pred C2) s sx -> Q sx) /\ (exists sx, (pred C2) s sx))).
    { apply (IHC1 _ _); auto; constructor; firstorder. }
    { apply (IHC2 _ _); auto; constructor; firstorder. }
  }
  { intros HHtriple; inversion_clear HHtriple; inversion BFC as [BFC1 BFC2]; clear BFC.
    constructor.
    { intros.
      destruct (H _ H0) as (_,(s',[(HHp,_) | (HHn,_) ])).
      { left; auto. }
      { right; auto. }
    }
    { apply (IHC1 _ _); auto; constructor; intros s (HHp1,HHp2); split; firstorder. }
    { apply (IHC2 _ _); auto; constructor; intros s (HHp1,HHp2); split; firstorder. }
  }
  { intros HHtriple; inversion_clear HHtriple; simpl in BFC.
    apply (While _ _ _ (fun s => (forall s', while p (pred C) s s' -> Q s') /\ exists s', while p (pred C) s s')
                 _ _ (fun s s' => p s' /\ pred C s' s /\ (exists r, (while p (pred C)) s' r))  (fun s => s)).
    { intros.
      destruct H0 as (_,(s',HHwhile)).
      apply while_destruct in HHwhile.
      destruct HHwhile as [ (HHp,_) | (HHn,_)]; unfold Decidable.decidable; auto.
    }
    {  constructor. 
      intros y [HHp [HHpred HHwhile]].
      generalize y HHp HHpred; clear y HHp HHpred.
      pattern a; apply (ex_while_ind _ _ _ _ HHwhile).
      intros.
      destruct H0; try contradiction.
      destruct H0.
      constructor; intros.
      destruct H2.
      destruct H3.
      apply (H1 y); auto.
    }
    { auto. }
    { intros.
      apply (IHC _ _); auto.
      constructor.
      intros.
      destruct H0 as (HH1,((HH2,(s',HH3)),HH)); subst v.
      apply while_destruct in HH3.
      destruct HH3 as [ (HH4,((sx,(HH51,HH52)),HH6)) | (HH4,HH5) ]; try contradiction. 
      split; intros.
      { split; intros. 
        { split; intros.
          { apply HH2.
            apply while_construct; left; split; auto.
            split.
            { exists s'0; firstorder. }
            { auto. }
          }
          { apply (HH6 _ H0). }
        }
        { split; auto.
          destruct (HH6 _ H0) as (s'',HH).
          split; auto.
          exists s''; apply while_construct; left; split; auto.
          split; eauto.
        }
      }
      { exists sx; auto. }
    }
    { intros.
      apply H1.
      apply while_construct; right; auto.
    }
  }
  { auto. }
  { simpl in BFC; contradiction. }
Qed.

Lemma hoare_pred :
  forall (T : Type) (C : @Stmt T) P Q, BlockFree C -> ValidHoareTriple P C Q <-> ValidHoareTriple P (Statement.Spec (pred C)) Q.
Proof.
  intros T C P Q BFC.
  split.
  { apply pred_if_hoare; auto. }
  { apply hoare_if_pred; auto. }
Qed.

Lemma pred_refines_iff_hoare_refines : forall T (Q R : T >> T),
    Predicative.refines (Statement.Spec Q) (Statement.Spec R) <-> FloydHoareWp.refines (Statement.Spec Q) (Statement.Spec R).
Proof.
  unfold Predicative.refines, FloydHoareWp.refines; intros; split; intros HHrefines.
  { intros K K' HHr.
    inversion_clear HHr.
    constructor.
    split; intros.
    { apply (H _ H0).
      apply HHrefines; auto.
      apply (H _ H0).
    }
    { apply HHrefines.
      apply (H _ H0).
    }
  }
  { intros.
    assert (ValidHoareTriple (fun r => r = s) (Statement.Spec R) (fun r' => R s r')).
    { constructor.
      intros r HHr.
      subst r.
      auto.
    }
    apply HHrefines in H0.
    inversion_clear H0.
    apply (H1 s (eq_refl s)).
  }
Qed.

Theorem hoare_refines_iff_pred_refines_simplified :
  forall T (Q R : @Stmt T), BlockFree Q -> BlockFree R -> FloydHoareWp.refines Q R <-> Predicative.refines Q R.
Proof.
  intros T Q R BFQ BFR.
  unfold FloydHoareWp.refines.
  setoid_rewrite (hoare_pred _ _ _ _ BFQ).
  setoid_rewrite (hoare_pred _ _ _ _ BFR).
  setoid_rewrite <- pred_refines_iff_hoare_refines.
  unfold Predicative.refines; simpl.
  reflexivity.
Qed.

Theorem pred_refines_if_hoare_refines :
  forall T (Q R : @Stmt T), BlockFree Q -> BlockFree R -> FloydHoareWp.refines Q R -> Predicative.refines Q R.
Proof.
  intros S Q R BFQ BFR; intros HHrefines.
  apply pred_refines_iff_hoare_refines.
  unfold FloydHoareWp.refines in *.
  intros Pre Post HHprepost.
  apply hoare_if_pred in HHprepost; auto.
  apply HHrefines in HHprepost.
  apply (pred_if_hoare _ Q); auto.
Qed.

Theorem hoare_refines_if_pred_refines :
  forall T (Q R : @Stmt T), BlockFree Q -> BlockFree R -> Predicative.refines Q R -> FloydHoareWp.refines Q R.
Proof.
  intros S Q R BFQ BFR; intros HHrefines.
  unfold FloydHoareWp.refines; intros Pre Post HHprepost.
  apply hoare_if_pred; auto.
  constructor.
  apply pred_if_hoare in HHprepost; auto.
  inversion_clear HHprepost.
  firstorder.
Qed.

(* The definition of refinement in Hoare Logic is equivalent to the predicative (relational) definition *)
Theorem hoare_refines_iff_pred_refines :
  forall T (Q R : @Stmt T), BlockFree Q -> BlockFree R -> FloydHoareWp.refines Q R <-> Predicative.refines Q R.
Proof.
  intros T Q R BFQ BFR.
  split; intros HHrefines.
  { apply pred_refines_iff_hoare_refines.
    unfold FloydHoareWp.refines in *.
    intros Pre Post HHprepost.
    apply hoare_pred in HHprepost; auto.
    apply (hoare_pred _ Q); auto.
  }
  { unfold FloydHoareWp.refines; intros Pre Post HHprepost.
    apply hoare_pred; auto.
    apply hoare_pred in HHprepost; auto.
    constructor.
    inversion_clear HHprepost.
    firstorder.
  }
Qed.

(* The definition of refinement with logical constants is equivalent to the definition without logical constants *)
Theorem extended_definition_iff_simple_definition : forall T S1 S2,
    BlockFree S1 -> BlockFree S2 -> 
    (forall (P Q : T -> Prop), P {: S1 :} Q -> P {: S2 :} Q)
    <-> (forall P (Q : T -> T -> Prop), (forall r, (fun s => r = s /\ P s) {: S1 :} (Q r)) -> forall r, (fun s => r = s /\ P s) {: S2 :} (Q r)).
Proof.
  intros * BFS1 BFS2.
  split.
  { intros.
    apply H.
    apply H0.
  }
  { setoid_rewrite (hoare_pred _ _ _ _ BFS1).
    setoid_rewrite (hoare_pred _ _ _ _ BFS2).
    intros.
    pose proof (H P (fun _ s' => Q s')).
    simpl in *.
    assert (forall r : T, (fun s : T => r = s /\ P s) {: Statement.Spec (Predicative.pred S1) :} (fun s' : T => Q s')).
    { intros.
      unshelve eapply (consequence _ _ _ _ _ _ _ _ H0); firstorder.
    }
    pose proof (H1 H2).
    setoid_rewrite hoare_pred; simpl; auto.
    constructor; intros.
    pose proof (H3 s).
    inversion_clear H5.
    apply H6.
    auto.
  }
Qed.

