Parameters p1 p2 t1 t2 : Prop.

Definition aff1 := p1 /\ t2.
Definition aff2 := (p1 /\ t2) \/ (p2 /\ t1).
Definition k := (aff1 /\ ~aff2) \/ (~aff1 /\ aff2).
Definition h1 := ~(p1 /\ t1) /\ ~(p2 /\ t2).
Definition h2 := (p1 \/ t1) /\ (p2 \/ t2).
 
Lemma epreuve_1 : h1 /\ h2 /\ k -> t1 /\ p2.
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
  
  left.
  split.
  assumption.
  assumption.

  destruct H2.
  destruct H4.  
  elimtype False.
  auto.

  destruct H4.
  split.
  assumption.
  assumption.
Qed.
