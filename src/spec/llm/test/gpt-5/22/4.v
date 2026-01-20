Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.

Definition Any := Z.
Definition int := Z.
Definition IsInt (v : Any) (n : int) : Prop := v = n.
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

Example test_case_all_ints: filter_integers_spec [1%Z; 2%Z; 3%Z; 4%Z; 5%Z] [1%Z; 2%Z; 3%Z; 4%Z; 5%Z].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int with (v:=1%Z) (n:=1%Z) (vs:=[2%Z; 3%Z; 4%Z; 5%Z]) (res:=[2%Z; 3%Z; 4%Z; 5%Z]).
  - reflexivity.
  - apply fir_cons_int with (v:=2%Z) (n:=2%Z) (vs:=[3%Z; 4%Z; 5%Z]) (res:=[3%Z; 4%Z; 5%Z]).
    + reflexivity.
    + apply fir_cons_int with (v:=3%Z) (n:=3%Z) (vs:=[4%Z; 5%Z]) (res:=[4%Z; 5%Z]).
      * reflexivity.
      * apply fir_cons_int with (v:=4%Z) (n:=4%Z) (vs:=[5%Z]) (res:=[5%Z]).
        { reflexivity. }
        { apply fir_cons_int with (v:=5%Z) (n:=5%Z) (vs:=[]) (res:=[]).
          - reflexivity.
          - constructor.
        }
Qed.