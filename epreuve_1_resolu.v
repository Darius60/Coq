Parameters p1 p2 t1 t2 : Prop.

Definition aff1 := p1 /\ t2.
Definition aff2 := (p1 /\ t2) \/ (p2 /\ t1).
Definition k := (aff1 /\ ~aff2) \/ (~aff1 /\ aff2).
Definition h1 := ~(p1 /\ t1) /\ ~(p2 /\ t2).
Definition h2 := (p1 \/ t1) /\ (p2 \/ t2).

Require Export Classical.
 
Lemma epreuve_1_bis : k -> t1 /\ p2.
Proof.
  unfold k.
  unfold aff1, aff2.
  intros.
  elim H; intros; clear H.
  elim H0; intros; clear H0.
  elimtype False.
  auto.
  elim H0; intros; clear H0.
  elim H1; intros; clear H1.
  elimtype False.
  auto.
  elim H0; intros; clear H0.
  split.
  assumption.
  assumption.
Qed.

Lemma epreuve_1_ter : k -> t1 /\ p2.
Proof.
  unfold k.
  unfold aff1, aff2.
  intros.
  elim H; intros; clear H.
  elim H0; intros; clear H0.
  elimtype False.
  apply H1.
  left; assumption.
  elim H0; intros; clear H0.
  elim H1; intros; clear H1.
  elimtype False.
  auto.
  elim H0; intros; clear H0.
  split; assumption.
Qed.

