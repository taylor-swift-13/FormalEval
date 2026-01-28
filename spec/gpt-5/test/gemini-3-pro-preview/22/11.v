Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Definition int := Z.
Parameter Any : Type.
Parameter inject_int : int -> Any.
Parameter IsInt : Any -> int -> Prop.

Axiom IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.
Axiom IsInt_inject : forall n, IsInt (inject_int n) n.

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

Example test_filter_integers : 
  filter_integers_spec 
    [inject_int 0%Z; inject_int 1%Z; inject_int 2%Z; inject_int 3%Z; inject_int 4%Z; 
     inject_int 5%Z; inject_int 6%Z; inject_int 7%Z; inject_int 8%Z; inject_int 9%Z]
    [0%Z; 1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z; 7%Z; 8%Z; 9%Z].
Proof.
  unfold filter_integers_spec.
  repeat (apply fir_cons_int; [ apply IsInt_inject | ]).
  apply fir_nil.
Qed.