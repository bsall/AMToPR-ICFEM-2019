Require Import Statement ThreadedPredicative Wfd.

Require Import Lia.

Open Scope stmt_scope.

Definition spec := ⟨fun '(i,n) '(i',n') => i <= n /\ i' = n /\ n = n'⟩.

Definition prog := WWhile (fun '(i,n) => i <> n) Do '(i,n) := (i+1,n) Done.

(* Proof of correctness by induction on n *)
Theorem correctness : prog ⊑ spec.
Proof.
  intros (i,n) ((u,v),(HHin,_)); clear u v.
  split.
  { intros (i',n') HHwhile.
    generalize HHin; clear HHin; simpl.
    cut ((fun '(i,n) '(i',n') =>  i <= n -> i <= n /\ i' = n /\ n = n') (i,n) (i',n')); auto.
    apply HHwhile; clear.
    intros (i,n) (i',n'); simpl.
    intros [ (HHin,HHind) | (HHin,HHeq) ] HHin'.
    { lia. }
    { inversion HHeq; subst i n; clear HHeq. lia. }
  }
  { generalize i HHin; clear i HHin; induction n; simpl in *.
    { exists (0,0); apply while_construct; right; split.
      { lia. }
      { f_equal; lia. }
    }
    { intros i HHiSn.
      apply Lt.le_lt_or_eq in HHiSn.
      destruct HHiSn as [ HHiSn | HHiSn ].
      { assert (i <= n) as HHin by lia.
        destruct (IHn _ HHin) as ((i',n'),HHwhile).
        set (Whl := while _ _) in *.
        exists (S i',S n').
        cut ((fun '(i,n) '(i',n') => i <= n -> Whl (i, S n) (S i', S n')) (i,n) (i',n')).
        { intros; auto. }
        apply (while_ind _ _ _ _ _ HHwhile).
        intros (j,m) (j',m'); simpl.
        intros.
        apply while_construct; fold Whl; simpl.
        destruct H.
        { destruct H.
          left; split; try lia.
          apply H1; lia.
        }
        { destruct H.
          inversion H1; subst j' m'.
          left; split; try lia.
          apply while_construct; right; split; try lia.
          f_equal; lia.
        }
      }
      { exists (S n,S n); apply while_construct; right; split; try lia.
        subst i; f_equal; lia.
      }
    }
  }
Qed.

(* Proof of correctness where well-founded-ness is proved by showing inclusion in a well founded relation*)

Theorem correctness2 : prog ⊑ spec.
Proof.
  set (new_body := (IIf (fun '(i,n) => i <= n) Then '(i,n) := (i+1,n) Else Statement.Void End)).
  eapply (refines_trans _ _ _ _ (While_monotonic_refines _ _ _ new_body _)).
  apply (refines_extensionality_left _ _ spec).
  { apply (wfd_fix_while _ _ (pred spec)).
    { clear.
      apply (Wfd.by_inclusion _ _ (fun '(i',n') '(i,n) => i < i' <= n /\ n' = n)).
      { intros (i,n).
        constructor; intros (i',n').
        remember (n-i) as v.
        generalize i i' n n' Heqv; clear i i' n n' Heqv.
        pattern v; apply (well_founded_ind Wf_nat.lt_wf).
        clear v; intros v HHind i i' n n' HHv HHin.
        assert (n-i' < v) by lia.
        pose proof (HHind (n-i') H).
        constructor; intros (i'',n'') HHi''n''.
        apply (H0 i' _ n); lia.
      }
      { intros (i,n) (i',n'); subst new_body; simpl.
        intros (HHin,[(HHi'n',HHeq) | (_,HHfalse)]).
        { inversion HHeq; clear HHeq; subst i n; lia. }
        { contradiction. }
      }
    }
    { intros (i,n) (i',n'); simpl; split.
      { intros (HHin,(HHi'n,HHnn')); subst i' n'.
        apply Lt.le_lt_or_eq in HHin.
        destruct HHin; try lia.
        subst i; right; auto. 
      }
      { intros [HH | (HHin,HHeq)].
        { firstorder. }
        { inversion HHeq; clear HHeq; subst i n. lia. }
      }
    }
  }
  { apply refines_reflexive. }
  Unshelve.
  firstorder. 
Qed.

(* Proof of correctness with the aid of a variant *)

Theorem correctness3 : prog ⊑ spec.
Proof.
  set (new_body := (IIf (fun '(i,n) => i <= n) Then '(i,n) := (i+1,n) Else Statement.Void End)).
  eapply (refines_trans _ _ _ _ (While_monotonic_refines _ _ _ new_body _)).
  apply (refines_extensionality_left _ _ spec).
  { apply (wfd_fix_while _ _ (pred spec)).
    { clear.
      apply (Wfd.by_inclusion _ _ (fun '(i',n') '(i,n) => i < i' <= n /\ n' = n)).
      { apply (Wfd.by_variant _ _ _ (fun '(i,n) => n - i) _ Wf_nat.lt_wf).
        intros (i',n') (i,n); simpl. lia.
      }
      { intros (i,n) (i',n'); subst new_body; simpl.
        intros (HHin,[(HHi'n',HHeq) | (_,HHfalse)]).
        { inversion HHeq; clear HHeq; subst i n; lia. }
        { contradiction. }
      }
    }
    { intros (i,n) (i',n'); simpl; split.
      { intros (HHin,(HHi'n,HHnn')); subst i' n'.
        apply Lt.le_lt_or_eq in HHin.
        destruct HHin; try lia.
        subst i; right; auto. 
      }
      { intros [HH | (HHin,HHeq)].
        { firstorder. }
        { inversion HHeq; clear HHeq; subst i n. lia. }
      }
    }
  }
  { apply refines_reflexive. }
  Unshelve.
  firstorder. 
Qed.

Close Scope stmt_scope.