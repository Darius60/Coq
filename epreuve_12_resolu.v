Parameters p1 p2 p3 p4 p5 p6 p7 p8 p9 t1 t2 t3 t4 t5 t6 t7 t8 t9: Prop.

Definition v1 := (~p1 /\ ~t1).
Definition v2 := (~p2 /\ ~t2).
Definition v3 := (~p3 /\ ~t3).
Definition v4 := (~p4 /\ ~t4).
Definition v5 := (~p5 /\ ~t5).
Definition v6 := (~p6 /\ ~t6).
Definition v7 := (~p7 /\ ~t7).
Definition v8 := (~p8 /\ ~t8).
Definition v9 := (~p9 /\ ~t9).

Definition aff1 := p1 \/ p3 \/ p5 \/ p7 \/ p9.
Definition aff2 := v2.
Definition aff4 := ~aff1.
Definition aff5 := aff2 \/ aff4.
Definition aff7 := ~p1.
Definition aff3 := aff5 \/ ~aff7.
Definition aff6 := ~aff3.
Definition aff8 := t8 /\ v9.
Definition aff9 := t9 /\ ~aff6.

Definition k := (p1 -> aff1) /\ (t1 -> ~aff1) /\ (p2 -> aff2) /\ (t2 -> ~aff2) /\ (p3 -> aff3) /\ (t3 -> ~aff3) /\
                (p4 -> aff4) /\ (t4 -> ~aff4) /\ (p5 -> aff5) /\ (t5 -> ~aff5) /\ (p6 -> aff6) /\ (t6 -> ~aff6) /\
                (p7 -> aff7) /\ (t7 -> ~aff7) /\ (p8 -> aff8) /\ (t8 -> ~aff8) /\ (p9 -> aff9) /\ (t9 -> ~aff9).

Definition h1 := ~(p1 /\ t1) /\ ~(p2 /\ t2) /\ ~(p3 /\ t3) /\
                ~(p4 /\ t4) /\ ~(p5 /\ t5) /\ ~(p6 /\ t6) /\
                ~(p7 /\ t7) /\ ~(p8 /\ t8) /\ ~(p9 /\ t9).

Definition tv1 := (t1 \/ v1).
Definition tv2 := (t2 \/ v2).
Definition tv3 := (t3 \/ v3).
Definition tv4 := (t4 \/ v4).
Definition tv5 := (t5 \/ v5).
Definition tv6 := (t6 \/ v6).
Definition tv7 := (t7 \/ v7).
Definition tv8 := (t8 \/ v8).
Definition tv9 := (t9 \/ v9).

Definition h2 := (p1 /\ tv2 /\ tv3 /\ tv4 /\ tv5 /\ tv6 /\ tv7 /\ tv8 /\ tv9)
              \/ (tv1 /\ p2 /\ tv3 /\ tv4 /\ tv5 /\ tv6 /\ tv7 /\ tv8 /\ tv9)
              \/ (tv1 /\ tv2 /\ p3 /\ tv4 /\ tv5 /\ tv6 /\ tv7 /\ tv8 /\ tv9)
              \/ (tv1 /\ tv2 /\ tv3 /\ p4 /\ tv5 /\ tv6 /\ tv7 /\ tv8 /\ tv9)
              \/ (tv1 /\ tv2 /\ tv3 /\ tv4 /\ p5 /\ tv6 /\ tv7 /\ tv8 /\ tv9)
              \/ (tv1 /\ tv2 /\ tv3 /\ tv4 /\ tv5 /\ p6 /\ tv7 /\ tv8 /\ tv9)
              \/ (tv1 /\ tv2 /\ tv3 /\ tv4 /\ tv5 /\ tv6 /\ p7 /\ tv8 /\ tv9)
              \/ (tv1 /\ tv2 /\ tv3 /\ tv4 /\ tv5 /\ tv6 /\ tv7 /\ p8 /\ tv9)
              \/ (tv1 /\ tv2 /\ tv3 /\ tv4 /\ tv5 /\ tv6 /\ tv7 /\ tv8 /\ p9).

Lemma epreuve_1_bis : h1 /\ h2 /\ k /\ t8 -> p7.
unfold k, h1, h2.
unfold aff9, aff6, aff3, aff5, aff4, aff1 , aff2, aff7, aff8.
unfold tv1, tv2, tv3, tv4, tv5, tv6, tv7, tv8 , tv9.
unfold v1, v2, v3, v4, v5, v6, v7, v8 , v9.
intros.
destruct H.
destruct H.
destruct H1.
destruct H2.
destruct H3.
destruct H4.
destruct H5.
destruct H6.
destruct H7.
destruct H0.
destruct H9.
destruct H9.
destruct H11.
destruct H12.
destruct H13.
destruct H14.
destruct H15.
destruct H16.
destruct H17.
destruct H18.
destruct H19.
destruct H20.
destruct H21.
destruct H22.
destruct H23.
destruct H24.
destruct H25.
destruct H26.

destruct H0.
destruct H0.
destruct H28.
destruct H29.
destruct H30.
destruct H31.
destruct H32.
destruct H33.
destruct H34.

elimtype False.
apply H25.
assumption.
split.
assumption.
destruct H35.

elimtype False.
apply H27.
assumption.
split.
assumption.
intro.
apply H36.
right.
intro.
apply H37.
assumption.
assumption.

destruct H0.
destruct H0.
destruct H28.
destruct H29.
destruct H30.
destruct H31.
destruct H32.
destruct H33.
destruct H34.

elimtype False.
apply H12.
assumption.
assert(H28bis := H28).
apply H12 in H28.
destruct H28.
elimtype False.
auto.

destruct H0.
destruct H0.
destruct H28.
destruct H29.
destruct H30.
destruct H31.
destruct H32.
destruct H33.
destruct H34.

assert(H14bis := H14).
assert(H29bis := H29).
apply H14 in H29.

elimtype False.
apply H25.
assumption.

split.
assumption.

destruct H35.
elimtype False.
apply H27.
assumption.
split.
assumption.
intro.
elimtype False.
auto.
assumption.

destruct H0.
destruct H0.
destruct H28.
destruct H29.
destruct H30.
destruct H31.
destruct H32.
destruct H33.
destruct H34.

assert(H30bis := H30).
assert(H16bis := H16).
apply H16 in H30.

elimtype False.
apply H25.
assumption.
split.
assumption.
destruct H35.
elimtype False.
apply H27.
assumption.
split.
assumption.
intro.
apply H36.
left.
right.
assumption.
assumption.

destruct H0.
destruct H0.
destruct H28.
destruct H29.
destruct H30.
destruct H31.
destruct H32.
destruct H33.
destruct H34.

assert(H31bis := H31).
assert(H18bis := H18).
apply H18 in H31.

elimtype False.
apply H25.
assumption.
split.
assumption.
destruct H35.
elimtype False.
apply H27.
assumption.
split.
assumption.
intro.
apply H36.
left.
assumption.
assumption.

destruct H0.
destruct H0.
destruct H28.
destruct H29.
destruct H30.
destruct H31.
destruct H32.
destruct H33.
destruct H34.

assert(H32bis := H32).
assert(H20bis := H20).
apply H20 in H32.

elimtype False.
apply H32.
left.
right.
intro.

destruct H36.
apply H25.
assumption.
split.
assumption.
destruct H35.
elimtype False.
apply H27.
assumption.
split.
assumption.
intro.
apply H37.
right.
intro.
auto.
assumption.

destruct H36.

assert(H14bis := H14).
assert(H36bis := H36).
apply H14 in H36.

elimtype False.
apply H25.
assumption.

split.
assumption.

destruct H35.
elimtype False.
apply H27.
assumption.
split.
assumption.
intro.
elimtype False.
auto.
assumption.

destruct H36.

assert(H18bis := H18).
assert(H36bis := H36).
apply H18 in H36.

apply H25.
assumption.
split.
assumption.
destruct H35.
elimtype False.
apply H27.
assumption.
split.
assumption.
intro.
auto.
assumption.

destruct H36.

assert(H22bis := H22).
assert(H36bis := H36).
apply H22 in H36.

apply H20.
assumption.
right.
apply H23.
destruct H33.
assumption.
destruct H33.
elimtype False.
auto.

apply H26.
assumption.
intro.
auto.

destruct H0.
destruct H0.
destruct H28.
destruct H29.
destruct H30.
destruct H31.
destruct H32.
destruct H33.
destruct H34.

assumption.

destruct H0.
destruct H0.
destruct H28.
destruct H29.
destruct H30.
destruct H31.
destruct H32.
destruct H33.
destruct H34.

elimtype False.
apply H24.
assumption.
destruct H35.
assumption.
destruct H35.
elimtype False.
auto.

destruct H0.
destruct H28.
destruct H29.
destruct H30.
destruct H31.
destruct H32.
destruct H33.
destruct H34.

assert(H26bis := H26).
assert(H35bis := H35).
apply H26 in H35.
destruct H35.

elimtype False.
apply H36.
intro.

apply H8.
split.
assumption.
assumption.

