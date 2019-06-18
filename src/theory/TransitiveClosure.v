Require Import Setoid.

Require Import LeastFixpoint Wfd AngelicComposition.

Definition ftcl { T : Type } (R : T -> T -> Prop) X := (fun s s' => (X ⊡ R) s s' \/ R s s').

Theorem ftcl_monotonic : forall T R (X Y : T -> T -> Prop) , (forall s s', X s s' -> Y s s') -> forall s s', ftcl R X s s' -> ftcl R Y s s' .
Proof. firstorder. Qed.

Definition tcl { T : Type } (R : T -> T -> Prop) := lfp (ftcl R).

Theorem tcl_fix : forall { T : Type } (R : T -> T -> Prop), forall s s', tcl R s s' <-> (tcl R ⊡ R) s s' \/ R s s'.
Proof.
  intros *.
  unfold tcl.
  setoid_rewrite (lfp_fix (ftcl R) (ftcl_monotonic _ R)).
  reflexivity.
Qed.

Theorem tcl_rotate : forall { T : Type } (R : T -> T -> Prop), forall s s', (R ⊡ tcl R) s s' <-> (tcl R ⊡ R) s s'.
Proof.
  intros *.
  split.
  { intros * (sx,(HH1,HH2)).
    generalize s HH1; clear s HH1.
    pattern sx,s'.
    apply HH2; clear sx s' HH2.
    intros.
    unfold ftcl in H.
    destruct H.
    { destruct H as (x,(H,H')).
      exists x; split; auto.
      apply tcl_fix; auto.
    }
    { exists s; split; auto.
      apply tcl_fix; auto.
    }
  }
  { intros (sx,(HHtcl,HH)).
    generalize s' HH; clear s' HH.
    pattern s,sx; apply HHtcl; clear s sx HHtcl.
    intros * [ HH | HH ].
    { destruct HH as (x,(HH1,HH2)).
      intros.
      destruct (HH1 _ HH2) as (y,(HH3,HH4)).
      exists y; split; auto.
      apply tcl_fix; left; exists s'; auto.
    }
    { intros.
      exists s'; split; auto.
      apply tcl_fix; auto.
    }
  }
Qed.

Theorem tcl_trans :  forall { T : Type } (R : T -> T -> Prop), forall s s', (tcl R ⊡ tcl R) s s' -> tcl R s s'.
Proof.
  intros * (sx,(HHtcl1,HHtcl2)).
  generalize s HHtcl1; clear s HHtcl1.
  pattern sx,s'.
  apply HHtcl2; clear sx s' HHtcl2.
  intros.
  unfold ftcl in H.
  apply tcl_fix; left.
  destruct H.
  { destruct H as (sx,(HH1,HH2)).
    apply HH1 in HHtcl1.
    exists sx; auto.
  }
  { exists s; auto. }
Qed.

Theorem tcl_inv : forall T (R : T -> T -> Prop), forall s s', tcl (fun s s' => R s' s) s s' <-> tcl R s' s.
Proof.
  intros*.
  split.
  { intros HHtcl.
    pattern s,s'; apply HHtcl; clear s s' HHtcl.
    intros * HHtcl.
    unfold ftcl in HHtcl.
    destruct HHtcl.
    { destruct H as (x,(H1,H2)).
      assert ((R ⊡ tcl R) s' s) by firstorder; clear H1 H2.
      rewrite tcl_rotate in H.
      apply tcl_fix.
      auto.
    }
    { apply tcl_fix; auto. }
  }
  { intros H.
    pattern s',s; apply H; clear s' s H.
    intros.
    destruct H.
    { destruct H as (x,(H1,H2)).
      assert (((fun s s' => R s' s) ⊡ tcl (fun s s' => R s' s)) s' s) by firstorder; clear H1 H2.
      rewrite tcl_rotate in H.
      apply tcl_fix.
      auto.
    }
    { apply tcl_fix; auto. }
  }
Qed.

Theorem tcl_wfd : forall T (R : T -> T -> Prop), well_founded R -> well_founded (tcl R).
Proof.
  intros.
  apply (Wfd.by_simulation _ _ _ (fun s s' => ((tcl R) s s' \/ s = s')) R); auto.
  { intros x _; exists x; auto. }
  { intros * HH.
    rewrite rdistr_or, <- (rneutral_eq _ _ (tcl R)) in HH.
    rewrite ldistr_or, <- (lneutral_eq _ _ R).
    rewrite <- tcl_fix.
    destruct HH; auto.
    apply (tcl_trans _ _ _ H0).
  }
Qed.

Theorem tcl_dom : forall T (R : T -> T -> Prop) s, (exists s', R s s') <-> (exists s', tcl R s s').
Proof.
  intros *.
  split.
  { intros (s',HHr).
    exists s'; rewrite tcl_fix.
    auto.
  }
  { intros (s',HHtcl).
    pattern s,s'.
    apply HHtcl.
    clear HHtcl s s'.
    intros.
    destruct H.
    { destruct H as (_,(H',_)). auto. }
    { eauto. }
  }
Qed.

Theorem tcl_ran : forall T (R : T -> T -> Prop) s', (exists s, R s s') <-> (exists s, tcl R s s').
Proof.
  intros *.
  split.
  { intros (s,HHr).
    exists s; rewrite tcl_fix.
    auto.
  }
  { intros (s,HHtcl).
    pattern s,s'.
    apply HHtcl.
    clear HHtcl s s'.
    intros.
    destruct H.
    { destruct H as (k,(_,H'')). eauto. }
    { eauto. }
  }
Qed.