Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope string_scope.

Inductive IsBinaryRepr : nat -> list bool -> Prop :=
  | BZ: IsBinaryRepr 0 [false]
  | B1: IsBinaryRepr 1 [true]
  | BEven (n : nat) (l : list bool) :
      n > 0 -> IsBinaryRepr n l -> IsBinaryRepr (2 * n) (l ++ [false])
  | BOdd (n : nat) (l : list bool) :
      n > 0 -> IsBinaryRepr n l -> IsBinaryRepr (2 * n + 1) (l ++ [true]).

Fixpoint binary_list_to_string (l : list bool) : string :=
  match l with
  | [] => ""
  | b :: tl => (if b then "1" else "0") ++ binary_list_to_string tl
  end.

Definition decimal_to_binary_spec (decimal : nat) (output : string) : Prop :=
  exists (bl : list bool),
    IsBinaryRepr decimal bl /\
    output = "db" ++ binary_list_to_string bl ++ "db".

Example decimal_to_binary_test_999999998 :
  decimal_to_binary_spec 999999998 "db111011100110101100100111111110db".
Proof.
  unfold decimal_to_binary_spec.
  exists [true; true; true; false; true; true; false; false; true; false; true; true; false; false; true; true; true; true; true; false].
  split.
  - (* Proof of IsBinaryRepr 999999998 [true; true; true; false; true; true; false; false; true; false; true; true; false; false; true; true; true; true; true; false] *)
    assert (IsBinaryRepr 499999999 [true; true; true; false; true; true; false; false; true; false; true; true; false; false; true; true; true; true; true]).
    {
      assert (IsBinaryRepr 249999999 [true; true; true; false; true; true; false; false; true; false; true; true; false; false; true; true; true; true]).
      {
        assert (IsBinaryRepr 124999999 [true; true; true; false; true; true; false; false; true; false; true; true; false; false; true; true; true]).
        {
          assert (IsBinaryRepr 62499999 [true; true; true; false; true; true; false; false; true; false; true; true; false; false; true; true]).
          {
            assert (IsBinaryRepr 31249999 [true; true; true; false; true; true; false; false; true; false; true; true; false; false; true]).
            {
              assert (IsBinaryRepr 15624999 [true; true; true; false; true; true; false; false; true; false; true; true; false; false]).
              {
                assert (IsBinaryRepr 7812499 [true; true; true; false; true; true; false; false; true; false; true; true; false]).
                {
                  assert (IsBinaryRepr 3906249 [true; true; true; false; true; true; false; false; true; false; true; true]).
                  {
                    assert (IsBinaryRepr 1953124 [true; true; true; false; true; true; false; false; true; false; true]).
                    {
                      assert (IsBinaryRepr 976562 [true; true; true; false; true; true; false; false; true; false]).
                      {
                        assert (IsBinaryRepr 488281 [true; true; true; false; true; true; false; false; true]).
                        {
                          assert (IsBinaryRepr 244140 [true; true; true; false; true; true; false; false]).
                          {
                            assert (IsBinaryRepr 122070 [true; true; true; false; true; true; false]).
                            {
                              assert (IsBinaryRepr 61035 [true; true; true; false; true; true]).
                              {
                                assert (IsBinaryRepr 30517 [true; true; true; false; true]).
                                {
                                  assert (IsBinaryRepr 15258 [true; true; true; false]).
                                  {
                                    assert (IsBinaryRepr 7629 [true; true; true]).
                                    {
                                      assert (IsBinaryRepr 3814 [true; true]).
                                      {
                                        assert (IsBinaryRepr 1907 [true]).
                                        {
                                          assert (IsBinaryRepr 953 [true]).
**