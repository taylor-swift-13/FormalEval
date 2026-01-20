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

Parameter val_2a val_1 val_one val_list123 val_map_six6 val_2b val_map_six6b : Any.
Parameter int_2a int_1 int_2b : int.
Axiom IsInt_val_2a : IsInt val_2a int_2a.
Axiom IsInt_val_1 : IsInt val_1 int_1.
Axiom NotInt_val_one : forall n, ~ IsInt val_one n.
Axiom NotInt_val_list123 : forall n, ~ IsInt val_list123 n.
Axiom NotInt_val_map_six6 : forall n, ~ IsInt val_map_six6 n.
Axiom IsInt_val_2b : IsInt val_2b int_2b.
Axiom NotInt_val_map_six6b : forall n, ~ IsInt val_map_six6b n.

Example test_case_mixed: filter_integers_spec [val_2a; val_1; val_one; val_list123; val_map_six6; val_2b; val_map_six6b] [int_2a; int_1; int_2b].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply IsInt_val_2a|].
  eapply fir_cons_int; [apply IsInt_val_1|].
  eapply fir_cons_nonint; [apply NotInt_val_one|].
  eapply fir_cons_nonint; [apply NotInt_val_list123|].
  eapply fir_cons_nonint; [apply NotInt_val_map_six6|].
  eapply fir_cons_int; [apply IsInt_val_2b|].
  eapply fir_cons_nonint; [apply NotInt_val_map_six6b|].
  constructor.
Qed.