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

Lemma epreuve_1_bis : h1 /\ h2 /\ k -> p7.
unfold k, h1, h2.
unfold aff9, aff6, aff3, aff5, aff4, aff1 , aff2, aff7, aff8.
unfold tv1, tv2, tv3, tv4, tv5, tv6, tv7, tv8 , tv9.
unfold v1, v2, v3, v4, v5, v6, v7, v8 , v9.
intros.