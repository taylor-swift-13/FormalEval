Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.

Parameter Any : Type.
Definition int : Type := Z.
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

Parameter v1 v2 v3 v4 v5 v6 v7 v8 : Any.
Axiom Iv1 : IsInt v1 1%Z.
Axiom v2_nonint : forall n, ~ IsInt v2 n.
Axiom v3_nonint : forall n, ~ IsInt v3 n.
Axiom v4_nonint : forall n, ~ IsInt v4 n.
Axiom Iv5 : IsInt v5 (-6)%Z.
Axiom Iv6 : IsInt v6 1%Z.
Axiom Iv7 : IsInt v7 88%Z.
Axiom Iv8 : IsInt v8 9%Z.

Example test_case_new: filter_integers_spec [v1; v2; v3; v4; v5; v6; v7; v8] [1%Z; (-6)%Z; 1%Z; 88%Z; 9%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply Iv1|].
  eapply fir_cons_nonint; [apply v2_nonint|].
  eapply fir_cons_nonint; [apply v3_nonint|].
  eapply fir_cons_nonint; [apply v4_nonint|].
  eapply fir_cons_int; [apply Iv5|].
  eapply fir_cons_int; [apply Iv6|].
  eapply fir_cons_int; [apply Iv7|].
  eapply fir_cons_int; [apply Iv8|].
  apply fir_nil.
Qed.