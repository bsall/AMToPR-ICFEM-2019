Require Import Lia Div2 Even PeanoNat.

Class St := mkSt { x : nat; r : nat; h : nat; m : nat }.

Require Import Statement Wpr Wfd CbC.

Definition sqr n := n * n.

Open Scope cbc_scope.
Open Scope stmt_scope.

Program Definition SquareRoot :=
  ⟨ fun '(mkSt x r h m) '(mkSt x' r' h' m')  => (sqr r' <= x < sqr (1 + r') /\ x = x') ⟩
  :{
      '(mkSt x r h m) ::= (mkSt x 0 (1 + x) m);;
      ⟨fun '(mkSt x r h m) '(mkSt x' r' h' m') => (sqr r <= sqr r' <= x /\ x < sqr h' <= sqr h) /\ x = x' /\ 1 + r' = h' ⟩ :{ 
        While (fun '(mkSt x r h m) => 1 + r <> h) Do
           ⟨ fun '(mkSt x r h m) '(mkSt x' r' h' m') => (sqr r <= sqr r' <= x /\ x < sqr h' <= sqr h) /\ (r < r' \/ h > h') /\ x = x' ⟩ 
            :{
               ⟨ fun '(mkSt x r h m) '(mkSt x' r' h' m') => r < m' < h /\ x = x' /\ r = r' /\ h = h' ⟩
               :{
                  '(mkSt x r h m) ::= (mkSt x r h (r + div2 (h - r))) 
                };;
                If (fun '(mkSt x r h m) => sqr m <= x) Then
                  '(mkSt x r h m) ::= (mkSt x m h m)
                Else
                 '(mkSt x r h m) ::= (mkSt x r m m)
                End
             }
        Done
     }
  }.

Fail Check SquareRoot.


Next Obligation.
  intros (x,r,h,m) ((x',r',h',m'),(HHrh,_)); simpl in *.
  split; auto.
  set (k := PeanoNat.Nat.div2 (h-r)).
  assert (2*r < 2*r + 2*k < 2*h).
  { rewrite <- (Nat.double_twice k).
    destruct (even_or_odd (h-r)); subst k.
    { rewrite <- (even_double _ H). lia. }
    { remember (h - r); destruct H.
      rewrite <- (even_div2 _ H), <- (even_double _ H).
      unfold sqr in *; nia.
    }
  }
  lia.
Qed.

Next Obligation.
  intros (x,r,h,m) ((x',r',h',m'),HH); simpl in *.
  split.
  { intros (xx,rx,hx,mx); simpl.
    intros [ HH1' [HH2 [HH3' HH4 ]]]; subst xx rx hx.
    assert (sqr mx <= x \/ sqr mx > x) as [ HH1 | HH1 ] by lia.
    { left; unfold sqr in *.
      split; auto; split; try lia.
      split.
      { split; try nia. }
      { split; auto; lia. }      
    }
    { right; split; try lia.
      split; try lia.
      unfold sqr in *. nia.
    }
  }
  { exists (mkSt x r h (r + 1)).
    repeat split; auto; try lia.
    unfold sqr in *; nia.
  }
Qed.

Next Obligation.
  split.
  { apply (Wfd.by_inclusion _ _ (fun '(mkSt x' r' h' m') '(mkSt x r h m)  =>
                                   r < h /\ (r < r' < h' /\ h' <= h \/ h' < h /\ r <= r' < h'))).
    { apply (Wfd.by_nat_variant _ _ (fun '(mkSt x r h m) => h - r)).
      intros (x,r,h,m) (x',r',h',m'). lia. 
    }
    { intros (x,r,h,m) (x',r',h',m').
      unfold sqr; nia. 
    }
  }
  { intros (x,r,h,m) (x',r',h',m') (HHrh2,(HHx,(HHrh3,HHeq))); subst x'.
    split.
    { intros (xx,rx,hx,mx) [ HH | (HH1,HH2) ].
      { unfold sqr in *; nia. }
      { inversion HH2; subst xx rx hx mx. lia. }
    }
    { assert (S r' = h' \/ S r' <> h') as [ HH | HH ] by lia.
      { exists (mkSt x r' h' m'); auto. }
      { assert (sqr (S r') <= x \/ x < sqr (S r')) as [ HH1 | HH1 ] by lia.
        { exists (mkSt x (S r') h' m'); left; split; auto. unfold sqr in *; nia. }
        {  exists (mkSt x r' (S r') m').
           left; split; auto.
           split; auto.
           { split.
             { split.
               { lia. }
               { clear HHrh3.
                 unfold sqr in *; nia.
               }
             }
             { split; auto.
               destruct HHx as (HHx1,HHx2).
               clear -HHx1 HHx2 HH.
               unfold sqr in *; nia.
             }
           }
           { split; auto; right; unfold sqr in *; nia. }
        }
      }
    }
  }
Qed.

Next Obligation.
  intros (x,r,h,m) ((x',r',h',m'),HH); simpl in *.
  destruct HH as ((HH1,HH2),(HH3,HH4)).
  assert (S r = h \/ S r <> h) by lia.
  destruct H.
  { right; split; auto; split; auto; split; auto.
    { subst; unfold sqr in *; nia. }
    { lia. }
  }
  { left; split; auto.
    split.
    { intros (xx,rx,hx,mx); intros ((HHx',(HHprog,HHxx)),HHrh); subst xx.
      split; auto; split; auto.
      lia.
    }
    { exists (mkSt x' r' h' m').
      split; auto.
      { unfold sqr in *.
        repeat split; auto.
        all : nia.
      }
    }
  }
Qed.

Next Obligation.
  intros (x,r,h,m) ((x',r',h',m'),(HH,HHx)); subst x'; simpl in *.
  split.
  { intros (xx,rx,hx,mx); intros ((HHx,HHx'),(HHprog,HHxx)); subst.
    unfold sqr in *; simpl; split; auto.
    nia.
  }
  { exists (mkSt x r' (S r') m').
    split; auto.
    { unfold sqr in *.
      split.
      { nia. }
      { split.
        { nia. }
        { assert (r' <= x) by nia.
          clear HH.
          nia.
        }
      }
    }
  }
Qed.

Definition proof : (Πc SquareRoot) ⊑ (Πa SquareRoot) := CbC.soundness SquareRoot.
Check proof. (*  →  proof : (Π2 SquareRoot) ⊑ (Π1 SquareRoot) *)
Print Assumptions proof. (* → Closed under the global context *)

Close Scope stmt_scope.
Close Scope cbc_scope.