Parameters p1 p2 t1 t2 : Prop.

Definition aff1 := p1 \/ p2.
Definition aff2 := p1.

Definition k := ((p1 /\ aff1) \/ (t1 /\ ~aff1)) /\ ((p2 /\ ~aff2) \/ (t2 /\ aff2)).

Definition h1 := ~(p1 /\ t1) /\ ~(p2 /\ t2).
Definition h2 := (p1 \/ t1) /\ (p2 \/ t2).

Lemma epreuve_1_bis : h1 /\ h2 /\ k -> p1 /\ t2.
Proof.
unfold k, h1, h2.
unfold aff1, aff2.
intros.
destruct H.
destruct H.
destruct H0.
destruct H0.
destruct H2.
destruct H2.
destruct H2.
destruct H4.
destruct H4.
elimtype False.
auto.
destruct H4.
split; assumption.
destruct H2.
elimtype False.
apply H5.
destruct H4.
destruct H4.
right.
assumption.
destruct H4.
left.
assumption.
