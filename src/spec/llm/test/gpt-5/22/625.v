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

Parameter obj_one_two : Any.
Parameter obj_empty1 : Any.
Parameter obj_five_six : Any.
Parameter obj_seven_eight : Any.
Parameter obj_empty2 : Any.

Axiom NonInt_obj_one_two : forall n, ~ IsInt obj_one_two n.
Axiom NonInt_obj_empty1 : forall n, ~ IsInt obj_empty1 n.
Axiom NonInt_obj_five_six : forall n, ~ IsInt obj_five_six n.
Axiom NonInt_obj_seven_eight : forall n, ~ IsInt obj_seven_eight n.
Axiom NonInt_obj_empty2 : forall n, ~ IsInt obj_empty2 n.

Example test_case_objects: filter_integers_spec [obj_one_two; obj_empty1; obj_five_six; obj_seven_eight; obj_empty2] [].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply NonInt_obj_one_two |].
  eapply fir_cons_nonint; [apply NonInt_obj_empty1 |].
  eapply fir_cons_nonint; [apply NonInt_obj_five_six |].
  eapply fir_cons_nonint; [apply NonInt_obj_seven_eight |].
  eapply fir_cons_nonint; [apply NonInt_obj_empty2 |].
  constructor.
Qed.