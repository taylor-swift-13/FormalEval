Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Parameter Any : Type.
Definition int := Z.
Parameter IsInt : Any -> int -> Prop.
Axiom IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.

Inductive filter_integers_rel : list Any -> list int -> Prop :=
| fir_nil : filter_integers_rel [] []
| fir_cons_int v n vs res :
    IsInt v n ->
    filter_integers_rel vs res ->
    filter_integers_rel (v :: vs) (n :: res)
| fir_cons_nonint v vs res :
    (forall n, ~ IsInt v n) ->
    filter_integers_rel vs res ->
    filter_integers_rel (v :: vs) res.

Definition filter_integers_spec (values : list Any) (res : list int) : Prop :=
  filter_integers_rel values res.

Parameters v10 x1 x2 x3 x4 v9_1 v9_2 x5 v9_3 x6 x7 x8 : Any.
Axiom Is_v10 : IsInt v10 10%Z.
Axiom Is_v9_1 : IsInt v9_1 9%Z.
Axiom Is_v9_2 : IsInt v9_2 9%Z.
Axiom Is_v9_3 : IsInt v9_3 9%Z.
Axiom Non_x1 : forall n, ~ IsInt x1 n.
Axiom Non_x2 : forall n, ~ IsInt x2 n.
Axiom Non_x3 : forall n, ~ IsInt x3 n.
Axiom Non_x4 : forall n, ~ IsInt x4 n.
Axiom Non_x5 : forall n, ~ IsInt x5 n.
Axiom Non_x6 : forall n, ~ IsInt x6 n.
Axiom Non_x7 : forall n, ~ IsInt x7 n.
Axiom Non_x8 : forall n, ~ IsInt x8 n.

Example test_case_new: filter_integers_spec [v10; x1; x2; x3; x4; v9_1; v9_2; x5; v9_3; x6; x7; x8] [10%Z; 9%Z; 9%Z; 9%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply Is_v10 |].
  eapply fir_cons_nonint; [apply Non_x1 |].
  eapply fir_cons_nonint; [apply Non_x2 |].
  eapply fir_cons_nonint; [apply Non_x3 |].
  eapply fir_cons_nonint; [apply Non_x4 |].
  eapply fir_cons_int; [apply Is_v9_1 |].
  eapply fir_cons_int; [apply Is_v9_2 |].
  eapply fir_cons_nonint; [apply Non_x5 |].
  eapply fir_cons_int; [apply Is_v9_3 |].
  eapply fir_cons_nonint; [apply Non_x6 |].
  eapply fir_cons_nonint; [apply Non_x7 |].
  eapply fir_cons_nonint; [apply Non_x8 |].
  apply fir_nil.
Qed.