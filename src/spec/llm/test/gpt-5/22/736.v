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

Parameter oneZ : Any.
Parameter list56 : Any.
Parameter empty_list : Any.
Parameter empty_record : Any.
Parameter str9 : Any.

Axiom IsInt_oneZ : IsInt oneZ 1%Z.
Axiom NotInt_list56 : forall n, ~ IsInt list56 n.
Axiom NotInt_empty_list : forall n, ~ IsInt empty_list n.
Axiom NotInt_empty_record : forall n, ~ IsInt empty_record n.
Axiom NotInt_str9 : forall n, ~ IsInt str9 n.

Example test_case_mixed: filter_integers_spec [oneZ; list56; empty_list; empty_record; str9] [1%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply IsInt_oneZ |].
  eapply fir_cons_nonint; [apply NotInt_list56 |].
  eapply fir_cons_nonint; [apply NotInt_empty_list |].
  eapply fir_cons_nonint; [apply NotInt_empty_record |].
  eapply fir_cons_nonint; [apply NotInt_str9 |].
  constructor.
Qed.