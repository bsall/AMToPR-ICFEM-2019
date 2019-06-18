Require Import Decidable.

Require Import Statement Wfd.

Inductive ValidHoareTriple { T : Type } : Predicate -> Stmt -> Predicate -> Prop :=

| Void : forall (P Q : Predicate), (forall s, ~ P s) -> ValidHoareTriple P Void Q
                                                                        
| Assignment :
    forall (effect : Effect) (P Q : Predicate),
      (forall s, P s -> Q (effect s))
      -> ValidHoareTriple P (Assignment effect) Q

| Seq :
    forall (P Q R : Predicate) (S1 S2 : Stmt),
    ValidHoareTriple P S1 Q
    -> ValidHoareTriple Q S2 R
    -> ValidHoareTriple P (Seq S1 S2) R

| If :
    forall (P Q : Predicate)(C : Predicate)(St Sf : Stmt),
      (forall s, P s -> decidable (C s))
    -> ValidHoareTriple (fun s => C s /\ P s) St Q
    -> ValidHoareTriple (fun s => ~ C s /\ P s) Sf Q
    -> ValidHoareTriple P (If C St Sf) Q

| While : forall (U : Type)(P Q I : Predicate)(C : Predicate)(B : Stmt)(R : U -> U -> Prop)(V : T -> U),
      (forall s, I s -> decidable (C s))
    -> well_founded R
    -> (forall s, P s -> I s)
    -> (forall v, ValidHoareTriple (fun s => C s /\ I s /\ v = V s) B (fun s => I s /\ R (V s) v))
    -> (forall s, ~ C s -> I s -> Q s)
    -> ValidHoareTriple P (While C B) Q

| Spec :
    forall (P Q : Predicate) (spec : Specification),
    (forall s , P s -> (forall s', spec s s' -> Q s') /\ (exists s', spec s s'))
    -> ValidHoareTriple P (Spec spec) Q.


Notation "P {: C :} Q" := (ValidHoareTriple P C Q) (at level 50, format "P  {:  C  :}  Q").

(* (refines S1 S2) is the proposition : S1 refines S2 *)
(* S1 refines S2 iff every specification satisfied by S2 is also satisfied by S1, i.e. S1 can safely replace S2 in all contexts *)
Definition refines { T : Type } (S1 S2 : @Stmt T) := forall P Q, P {: S2 :} Q -> P {: S1 :} Q.

Notation "C1 ⊑ C2" := (refines C1 C2) (at level 60, format "C1  ⊑  C2").

Theorem skip_left_neutral : forall T S (P Q : T -> Prop), BlockFree S -> P {: S :} Q <-> P {: Skip;S :} Q.
Proof.
  intros T S P Q BFS.
  split.
  { intros HHtriple.
    apply (Seq _ P).
    { constructor; auto. }
    { exact HHtriple. }
  }
  { generalize P Q; clear P Q.
    induction S.
    { intros * HH; inversion_clear HH.
      inversion_clear H; inversion_clear H0.
      constructor.
      firstorder.
    }
    { intros * HH; inversion_clear HH; inversion_clear H; inversion_clear H0; inversion_clear BFS.
      constructor.
      firstorder.
    }
    { intros * HH; inversion_clear HH; inversion_clear H; inversion_clear H0; inversion_clear BFS.
      apply (Seq _ Q1); auto.
      apply IHS1; auto.
      apply (Seq _ Q0); auto.
      constructor; auto.
    }
    { intros * HH; inversion_clear HH; inversion_clear H; inversion_clear H0; inversion_clear BFS.
      constructor; auto.
      { apply IHS1; auto.
        apply (Seq _ (fun s => p s /\ Q0 s)); auto.
        constructor; firstorder.
      }
      { apply IHS2; auto.
        apply (Seq _ (fun s => ~ p s /\ Q0 s)); auto.
        constructor; firstorder.
      }
    }
    { intros * HH; inversion_clear HH; inversion_clear H; inversion_clear H0; simpl in BFS.
      apply (While _ P Q I p S R V); auto.
    }
    { intros * HH; inversion_clear HH; inversion_clear H; inversion_clear H0; simpl in BFS.
      constructor; auto.
    }
    { inversion_clear BFS; contradiction. }
  }
Qed.

Theorem skip_right_neutral : forall T S (P Q : T -> Prop), BlockFree S -> P {: S :} Q <-> P {: S;Skip :} Q.
Proof.
  intros T S P Q BFS.
  split.
  { intros HHtriple.
    apply (Seq _ Q); auto.
    constructor; auto. 
  }
  { generalize P Q; clear P Q.
    induction S.
    { intros * HH; inversion_clear HH.
      inversion_clear H; inversion_clear H0.
      constructor.
      firstorder.
    }
    { intros * HH; inversion_clear HH; inversion_clear H; inversion_clear H0; inversion_clear BFS.
      constructor.
      firstorder.
    }
    { intros * HH; inversion_clear HH; inversion_clear H; inversion_clear H0; inversion_clear BFS.
      apply (Seq _ Q1); auto.
      apply IHS2; auto.
      apply (Seq _ Q0); auto.
      constructor; auto.
    }
    { intros * HH; inversion_clear HH; inversion_clear H; inversion_clear H0; inversion_clear BFS.
      constructor; auto.
      { apply IHS1; auto.
        apply (Seq _ Q0); auto.
        constructor; firstorder.
      }
      { apply IHS2; auto.
        apply (Seq _ Q0); auto.
        constructor; firstorder.
      }
    }
    { intros * HH; inversion_clear HH; inversion_clear H; inversion_clear H0; simpl in BFS.
      apply (While _ P Q I p S R V); auto.
    }
    { intros * HH; inversion_clear HH; inversion_clear H; inversion_clear H0; simpl in BFS.
      constructor; firstorder.
    }
    { inversion_clear BFS; contradiction. }
  }
Qed.

(* The classical rule of consequence is derivable *)
Theorem consequence : forall T (P P' Q Q' : @Predicate T) (S : @Stmt T),
    BlockFree S -> (forall s, P s -> P' s) -> P' {: S :} Q' -> (forall s, Q' s -> Q s) -> P {: S :} Q.
Proof.
  intros.
  apply skip_left_neutral; auto.
  apply (Seq _ P').
  { constructor; auto. }
  { apply skip_right_neutral; auto.
    apply (Seq _ Q').
    { auto. }
    { constructor; auto. }
  }
Qed.    
