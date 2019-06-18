Require Import Setoid.

Require Import Statement.

Definition monotonic { T U : Type } (f : T >> U -> T >> U) :=
  forall (X1 X2 : T >> U), (forall s s', X1 s s' -> X2 s s') -> (forall s s', f X1 s s' -> f X2 s s').

Definition chain { T U : Type } (C : T >> U -> Prop) :=
  forall X Y, C X -> C Y -> (forall s s',X s s' -> Y s s') \/ (forall s s',Y s s' -> X s s').

Definition exists_continuous { T U : Type } (f : T >> U -> T >> U) :=
  forall (C : T >> U -> Prop),
    chain C
    ->  chain (fun e' => exists e, C e /\ forall s s', f e s s' <-> e' s s')
       /\ forall s s', f (fun s s' => exists e, C e /\ e s s') s s' <-> (exists e, C e /\ f e s s'). 

Theorem exists_continuous_monotonic :
  forall { T U : Type } (f : T >> U -> T >> U),
    (forall X Y, (forall s s', X s s' <-> Y s s') -> (forall s s', f X s s' <-> f Y s s'))
    -> exists_continuous f -> monotonic f.
Proof.
  intros * HHext HH X Y HHimpl s s' HHfx.
  destruct (HH (fun Z => (forall s s', Z s s' <-> X s s') \/ (forall s s', Z s s' <-> Y s s'))).
  { unfold chain. intros A B HH1 HH2.
    destruct HH1, HH2; setoid_rewrite H; setoid_rewrite H0; auto.
  }
  { cut (forall s s', (exists e : Specification,
            ((forall s1 s'1, e s1 s'1 <-> X s1 s'1) \/ (forall s1 s'1, e s1 s'1 <-> Y s1 s'1)) /\
            e s s') <-> Y s s').
    { intros.
      apply (HHext _ _ H1).
      apply H0.
      exists X; split; auto.
      left. reflexivity.
    }
    { intros r r'.
      split.
      { intros (e,([HHeq | HHeq],HHe)).
        { apply HHimpl; rewrite <- HHeq; exact HHe. }
        { apply HHeq; exact HHe. }
      }
      { intros HHy; exists Y; split; auto; right; reflexivity. }
    }
  }
Qed.

Definition lfp { T U : Type } (f : T >> U -> T >> U) :=
  fun s s' => forall X, (forall s s', f X s s' -> X s s') -> X s s'.

Theorem lfp_extensionality : forall { T U : Type } F G, (forall (X : T >> U) s s', F X s s' <-> G X s s')
                                                  -> forall s s', lfp F s s' <-> lfp G s s'.
Proof.
  intros.
  unfold lfp.
  split; intros.
  { apply H0.
    intros; apply H1.
    rewrite <- H.
    exact H2.
  }
  { apply H0.
    intros; apply H1.
    rewrite H.
    exact H2.
  }
Qed.

Theorem f_lfp : forall { T U : Type } (f : T >> U -> T >> U)  X,
    (forall s s', f X s s' -> X s s') -> (forall s s', (lfp f) s s' -> X s s').
Proof. firstorder. Qed.

Theorem f_lfp_lfp : forall { T U : Type } (f : T >> U -> T >> U),
    (monotonic f) -> forall s s', f (lfp f) s s' -> (lfp f) s s'.
Proof.
  intros T U f HHmonotonic s s' HHf.
  unfold lfp.
  intros X HHf'.
  apply HHf'.
  apply (HHmonotonic _ _ (f_lfp _ _ HHf') _ _ HHf).
Qed.

Theorem lfp_f_lfp : forall { T U : Type } (f : T >> U -> T >> U),
    (monotonic f) -> forall s s', (lfp f) s s' -> f (lfp f) s s'.
Proof.
  intros T U f HHmonotonic s s' HHlfp.
  apply HHlfp.
  intros r r' HHf.
  apply (HHmonotonic _ _ (f_lfp_lfp _ HHmonotonic) _ _ HHf).
Qed.

Theorem lfp_fix : forall { T U : Type } (f : T >> U -> T >> U),
    (monotonic f) -> forall s s', f (lfp f) s s' <-> (lfp f) s s'.
Proof.
  intros T U f HHmonotonic s s'; split.
  { apply (f_lfp_lfp _ HHmonotonic). }
  { apply (lfp_f_lfp _ HHmonotonic). }
Qed.

Opaque lfp.

  