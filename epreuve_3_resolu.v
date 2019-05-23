Parameters p1 p2 t1 t2 : Prop.

Definition aff1 := t1 \/ ~t1 /\ p2.
Definition aff2 := p1.
Definition k := (aff1 /\ aff2) \/ (~aff1 /\ ~aff2).

Definition h1 := ~(p1 /\ t1) /\ ~(p2 /\ t2).
Definition h2 := (p1 \/ t1) /\ (p2 \/ t2).

Lemma epreuve_3 : h1 /\ h2 /\ k -> p1 /\ p2.
Proof.
unfold k, h1, h2.
unfold aff1, aff2.
intros.

destruct H.
destruct H0.
destruct H.
destruct H0.

destruct H1.
destruct H1.
destruct H1.
elimtype False.
auto.

destruct H1.
split. 
assumption.
assumption.

destruct H1.
destruct H0.
elimtype False.
auto.
elimtype False.
auto.

Qed.