Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

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

Parameter Any_of_Z : Z -> Any.
Parameter Any_of_string : string -> Any.
Parameter Any_of_list : list Any -> Any.

Definition innerA := [Any_of_Z 1%Z; Any_of_string "2"%string; Any_of_string "2"%string].
Definition innerB := [Any_of_Z 5%Z; Any_of_string "six"%string; Any_of_Z 5%Z; Any_of_string "six"%string].
Definition innerC := [Any_of_string "3"%string; Any_of_Z 4%Z].
Definition innerD := ([] : list Any).
Definition innerE := [Any_of_string "seven"%string; Any_of_string "8"%string].

Axiom NotInt_innerA : forall n, ~ IsInt (Any_of_list innerA) n.
Axiom NotInt_innerB : forall n, ~ IsInt (Any_of_list innerB) n.
Axiom NotInt_innerC : forall n, ~ IsInt (Any_of_list innerC) n.
Axiom NotInt_innerD : forall n, ~ IsInt (Any_of_list innerD) n.
Axiom NotInt_innerE : forall n, ~ IsInt (Any_of_list innerE) n.

Example test_case_nested_lists:
  filter_integers_spec
    [Any_of_list innerA;
     Any_of_list innerB;
     Any_of_list innerA;
     Any_of_list innerC;
     Any_of_list innerB;
     Any_of_list innerD;
     Any_of_list innerA;
     Any_of_list innerE;
     Any_of_list innerB]
    [].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [exact NotInt_innerA|].
  eapply fir_cons_nonint; [exact NotInt_innerB|].
  eapply fir_cons_nonint; [exact NotInt_innerA|].
  eapply fir_cons_nonint; [exact NotInt_innerC|].
  eapply fir_cons_nonint; [exact NotInt_innerB|].
  eapply fir_cons_nonint; [exact NotInt_innerD|].
  eapply fir_cons_nonint; [exact NotInt_innerA|].
  eapply fir_cons_nonint; [exact NotInt_innerE|].
  eapply fir_cons_nonint; [exact NotInt_innerB|].
  constructor.
Qed.