Parameters p1 p2 p3 t1 t2 t3 : Prop.

Definition aff1 := t1.
Definition aff2 := p2.
Definition aff3 := t2.

Definition k := (aff1 /\ ~aff2 /\ ~aff3) \/ (~aff1 /\ aff2 /\ ~aff3) \/ (aff1 /\ ~aff2 /\ ~aff3).

Definition h1 := ~(p1 /\ t1) /\ ~(p2 /\ t2) /\ ~(p3 /\ t3).
Definition h2 := (p1 \/ t1) /\ (p2 \/ t2) /\ (p3 \/ t3).
Definition h3 := (p1 /\ t2 /\ t3) \/ (t1 /\ p2 /\ t3) \/ (t1 /\ t2 /\ p3).

Lemma epreuve_1_bis : h1 /\ h2 /\ h3 /\ k -> p1 /\ t2 /\ t3.
Proof.
unfold k, h1, h2, h3.
unfold aff1, aff2, aff3.
intros.
destruct H.
destruct H.
destruct H1.
destruct H0.
destruct H0.
destruct H4.
destruct H3.
destruct H3.
destruct H3.
destruct H7.
destruct H6.
destruct H6.
destruct H9.
elimtype False.
apply H.
split; assumption.
destruct H6.
destruct H6.
destruct H9.
elimtype False.
apply H1.
split; assumption.
destruct H6.
destruct H9.
elimtype False.
apply H.
split; assumption.
destruct H3.
destruct H3.
destruct H7.
destruct H6.
destruct H6.
destruct H9.
elimtype False.
apply H9.
assumption.
destruct H6.
destruct H6.
destruct H9.
elimtype False.
apply H6.
assumption.
destruct H6.
destruct H9.
elimtype False.
apply H9.
assumption.
destruct H3.
destruct H7.
destruct H6.
destruct H6.
destruct H9.
elimtype False.
apply H10.
assumption.
destruct H6.
destruct H6.
destruct H9.
elimtype False.
apply H10.
assumption.
destruct H6.
destruct H9.
elimtype False.
apply H10.
assumption.