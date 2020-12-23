Inductive term : Type :=
| Var : nat -> term (* Let's work with DeBruijn for now. Might want to consider using autosubst2 once things get serious *)

| App : term -> term -> term

| Lam : term -> term
.

