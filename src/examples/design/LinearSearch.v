Class St := mkSt { i : nat; n : nat; a : nat -> nat; x : nat}.

Require Import Statement Wpr Wfd CbC.

Require Import Lia.

Open Scope cbc_scope.
Open Scope stmt_scope.

Program Definition LinearSearch :=
  ⟨ fun '(mkSt i n a x) '(mkSt i' n' a' x')  => ((forall k, k < n -> a k <> x) \/ i' < n /\ a i' = x) /\ a = a' /\ x = x' ⟩
  :{ '(mkSt i n a x) ::= (mkSt 0 n a x);;
      IIf (fun '(mkSt i n a x) => i <> n) Then ⟨ fun '(mkSt i n a x) '(mkSt i' n' a' x') => i < n /\ ((forall k, i <= k < n -> a k <> x) \/ i' < n /\ a i' = x) /\ a = a' /\ x = x' /\ i' = n' ⟩ End :{
        While (fun  '(mkSt i n a x)  => i <> n) Do
          ⟨ fun '(mkSt i n a x) '(mkSt i' n' a' x') => i < n /\ a' = a /\ x' = x /\
                                      (i < i' <= n /\ (forall k, i <= k < i' -> a k <> x) /\ n = n' \/ i' < n /\ a i' = x /\ n' = i') ⟩
          :{ If (fun '(mkSt i n a x) => a i <> x) Then
             '(mkSt i n a x) ::= (mkSt (i + 1) n a x)
             Else
              '(mkSt i n a x) ::= (mkSt i i a x)
             End
           }
        Done
     }
  }.

Next Obligation.
 intros (i,n,a,x) ((j,m,b,y),HH); simpl in HH.
 simpl.
 assert (a i = x \/ a i <> x) as [ HHax | HHax ] by lia.
 { right; split; auto.
   split.
   { clear - HH; lia. }
   { split; auto; split; auto; right.
     split; auto. lia.
   }
 }
 { left; split; auto.
   split.
   { clear -HH; lia. }
   { split; auto; split; auto.
     left; split.
     { clear -HH; lia. }
     { split; auto.
       intros k HHk.
       assert (k = i) by (clear -HHk; lia).
       rewrite H; auto.
     }
   }
 }
Qed.

Next Obligation.
  split.
  { apply (Wfd.by_inclusion _ _ (fun '(mkSt i' n' a' x') '(mkSt i n a x)  => i < i' <= n /\ n = n' \/ i < n /\ i = i' /\ n' = i)).
    { apply (Wfd.by_nat_variant _ _ (fun '(mkSt i n a x) => n - i)).
      intros (i,n,a,x) (j,m,b,y) H.
      lia.
    }
    { intros (i,n,a,x) (j,m,b,y) H.
      repeat (match goal with [ H : _ /\ _  |- _ ] => destruct H | [ H : _ \/ _ |- _ ] => destruct H end); subst n.
      { lia. }
      { clear -H1; lia. }
    }
  }
  { intros (i,n,a,x) (i',n',a',x') (HHin,(HHin2,(HHa,(HHx,HH)))); subst a' x'.
    split.
    { intros (ix,nx,ax,xx); simpl.
      intros [(_,(HHi'n',(HHa,(HHx,HH2)))) | (HH11,HH12) ].
      { subst ax xx.
        split; auto. split; auto; split; auto; split; auto.
        assert (n' <= n)as HHn'n by lia.
        destruct HH as [ (HHii',(HHak,HHnn')) | (_,(_,HHi'n'2)) ]; subst n'.
        { destruct HH2 as [ (HHx1,(HHx2,HHx3)) | HHx ].
          { subst nx.
            left; split; try lia.
            split; auto.
            intros k HHk.
            assert (k < i' \/ i' <= k) by lia.
            destruct H.
            { apply HHak; lia. }
            { apply HHx2; lia. }
          }
          { right; auto. }
        }
        { clear -HHi'n'; lia. }
      }
      { inversion HH12; subst ix nx ax xx; clear HH12.
        split; auto.
      }
    }
    { assert (i' = n' \/ i' <> n') by lia.
      destruct H.
        { subst n'; exists (mkSt i' i' a x); auto. }
        { destruct HH. 
          { assert (a i' = x \/ a i' <> x) by lia.
            destruct H1.
            { exists (mkSt i' i' a x); left; split; auto.
              split.
              { lia. }
              { split; auto; split; auto; right; split; auto. lia. }
            }
            { exists (mkSt (i' + 1) n' a x).
              left; split; auto; split.
              { lia. } 
              { split; auto; split; auto; left; split.
                { lia. }
                { split; auto. 
                  clear -H1; intros k HHk.
                  assert (k = i') by lia; subst k; auto.
                }
              }
            }
          }
          { destruct H0 as (_,(_,H1)).
            subst i'. contradict H; auto.
          }
        }
      }
    }
Qed.  

Next Obligation.
  intros (i,n,a,x) ((ix,nx,ax,xx),HHdom); simpl in *.
  unfold wpr_spec; simpl.
  destruct HHdom.
  { left.
    destruct H as (H1,(H2,(H3,(H4,H5)))); subst.
    split; auto.
    split.
    { intros (i',n',a',x') HH.
      left; split; firstorder.
    }
    { destruct H3.
      { exists (mkSt n n ax xx).
        firstorder.
      }
      { exists (mkSt ix nx ax xx).
        firstorder.
      }
    }
  }
  { right.
    destruct H.
    inversion H0; subst; clear H0.
    auto.
  }
Qed.
  
Next Obligation.
  intros (i,n,a,x) ((ix,nx,ax,xx),HHdom); simpl in *.
  unfold wpr_spec; simpl.
  assert (n = 0 \/ n <> 0) as [HHn0 | HHn0] by lia.
  { right; subst n.
    repeat (match goal with |- _ /\ _ => split end); auto.
    left; intros k HHk. clear -HHk; lia.
  }
  { left; split; auto.
    split.
    { intros (i',n',a',x')  (_,(HHind,(HHa,(HHx,HH2)))).
      subst a' x'; split; auto.
      subst i'.
      destruct HHind as [ HHak | (HHn'n,HHan') ]; auto.
      left; intros k HHk.
      apply HHak; clear -HHk; lia.
    }
    {  destruct HHdom as ([ HHnotfound | (HHj1,HHj2) ],_).
       { exists (mkSt n n a x); split; auto.
         { clear -HHn0; lia. }
         { split; auto; left.
           intros k HHk.
           apply HHnotfound; clear -HHk; lia.
         }
       }
       { exists (mkSt ix ix a x); split; auto.
         lia.
       }
    }
  }
Qed.

Theorem proof : (Πc LinearSearch) ⊑ (Πa LinearSearch).
Proof. apply (CbC.soundness LinearSearch). Qed.

Check proof.
Print Assumptions proof.

Close Scope stmt_scope.
Close Scope cbc_scope.

