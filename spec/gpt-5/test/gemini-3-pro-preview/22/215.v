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

(* Parameters for the test case values *)
(* Input list corresponds to: [1; [2; 3]; 4; [5]; 91; []; [7; "8"]; "9"; {}; 1] *)
Parameter v1 : Any. Axiom v1_is_int : IsInt v1 1%Z.
Parameter v2 : Any. Axiom v2_not_int : forall n, ~ IsInt v2 n. (* [2; 3] *)
Parameter v3 : Any. Axiom v3_is_int : IsInt v3 4%Z.
Parameter v4 : Any. Axiom v4_not_int : forall n, ~ IsInt v4 n. (* [5] *)
Parameter v5 : Any. Axiom v5_is_int : IsInt v5 91%Z.
Parameter v6 : Any. Axiom v6_not_int : forall n, ~ IsInt v6 n. (* [] *)
Parameter v7 : Any. Axiom v7_not_int : forall n, ~ IsInt v7 n. (* [7; "8"] *)
Parameter v8 : Any. Axiom v8_not_int : forall n, ~ IsInt v8 n. (* "9" *)
Parameter v9 : Any. Axiom v9_not_int : forall n, ~ IsInt v9 n. (* {} *)
Parameter v10 : Any. Axiom v10_is_int : IsInt v10 1%Z.

Example test_filter_integers : 
  filter_integers_spec [v1; v2; v3; v4; v5; v6; v7; v8; v9; v10] [1%Z; 4%Z; 91%Z; 1%Z].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int with (n := 1%Z). apply v1_is_int.
  apply fir_cons_nonint. apply v2_not_int.
  apply fir_cons_int with (n := 4%Z). apply v3_is_int.
  apply fir_cons_nonint. apply v4_not_int.
  apply fir_cons_int with (n := 91%Z). apply v5_is_int.
  apply fir_cons_nonint. apply v6_not_int.
  apply fir_cons_nonint. apply v7_not_int.
  apply fir_cons_nonint. apply v8_not_int.
  apply fir_cons_nonint. apply v9_not_int.
  apply fir_cons_int with (n := 1%Z). apply v10_is_int.
  apply fir_nil.
Qed.