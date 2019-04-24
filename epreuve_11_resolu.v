Parameters p1 p2 p3 t1 t2 t3: 

Prop.

Definition v1 := (~p1 /\ ~t1).
Definition v2 := (~p2 /\ ~t2).
Definition v3 := (~p3 /\ ~t3).

Definition aff1 := v3.
Definition aff2 := t1.
Definition aff3 := v3.

Definition k2 := (aff1 /\ ~aff2 /\ ~aff3) \/ (aff1 /\ aff2 /\ ~aff3) \/ (aff1 /\ ~aff2 /\ ~aff3).

Definition k := (p1 -> aff1) /\ (t1 -> ~aff1) /\ (p2 -> aff2) /\ (t2 -> ~aff2) /\ (p3 -> aff3) /\ (t3 -> ~aff3).

Definition h1 := ~(p1 /\ t1) /\ ~(p2 /\ t2) /\ ~(p3 /\ t3).

Definition h2 := (p1 /\ t2 /\ v3) \/ (p1 /\ v2 /\ t3) 
                \/ (t1 /\ p2 /\ v3) \/ (t1 /\ v2 /\ p3)
                \/ (v1 /\ p2 /\ t3) \/ (v1 /\ t2 /\ p3).

Lemma epreuve_1_bis : h1 /\ h2 /\ k -> p1 /\ t2 /\ v3.

Proof.
unfold k, h1, h2.
unfold aff1, aff2, aff3.
unfold v1, v2, v3.
intros.

destruct H.
destruct H.
destruct H1.
destruct H0.
destruct H3.
destruct H4.
destruct H5.
destruct H6.
destruct H7.

destruct H0.
auto.

destruct H0.
destruct H0.
destruct H9.

elimtype False.
apply H3.
assumption.
assumption.

destruct H0.
destruct H0.
destruct H9.
elimtype False.
apply H4.
assumption. 
assumption.
destruct H0.
destruct H0.
destruct H9.

elimtype False.
apply H4.
assumption.
apply H7.
assumption.

destruct H0.
destruct H0.
destruct H0.
destruct H9.

destruct H4.
apply H5.
assumption.
elim H8.
assumption.
auto.

destruct H0.
destruct H0.
destruct H9.
destruct H7.
assumption.
elimtype False.
auto.