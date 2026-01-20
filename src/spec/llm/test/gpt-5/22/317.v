Require Import Coq.Lists.List.
Import ListNotations.

Parameter Any : Type.
Parameter int : Type.
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

Parameter v1 : Any.
Parameter v4list : Any.
Parameter v5list : Any.
Parameter v9 : Any.
Parameter n1 : int.
Parameter n9 : int.

Axiom IsInt_v1 : IsInt v1 n1.
Axiom IsInt_v9 : IsInt v9 n9.
Axiom NonInt_v4list : forall n, ~ IsInt v4list n.
Axiom NonInt_v5list : forall n, ~ IsInt v5list n.

Example test_case_mixed: filter_integers_spec [v1; v4list; v5list; v9; v9] [n1; n9; n9].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply IsInt_v1|].
  eapply fir_cons_nonint; [apply NonInt_v4list|].
  eapply fir_cons_nonint; [apply NonInt_v5list|].
  eapply fir_cons_int; [apply IsInt_v9|].
  eapply fir_cons_int; [apply IsInt_v9|].
  apply fir_nil.
Qed.