app [main] { pf: platform "https://github.com/roc-lang/basic-cli/releases/download/0.10.0/vNe6s9hWzoTZtFmNkvEICPErI9ptji_ySjicO6CkucY.tar.br" }

import pf.Stdout

main =

    # Program
    varInc = @Var "inc"
    varAdd = @Var "add"
    varX = @Var "x"
    varY = @Var "y"
    prog =
        Lam {
            arg: varX,
            body: Let {
                var: varY,
                val: Int 3,
                res: App {
                    fn: App {
                        fn: Var varAdd,
                        arg: Var varY,
                    },
                    arg: Var varX,
                },
            },
        }

    stdlib = Dict.fromList [
        (Var varInc, Lam { arg: Int, res: Int }),
        (Var varAdd, Lam { arg: Int, res: Lam { arg: Int, res: Int } }),
    ]

    (_, type) = infer stdlib prog
    Stdout.line! "Result: $(printType type)"

Expr : [
    Int U64,
    Var Var,
    Lam { arg : Var, body : Expr },
    App { fn : Expr, arg : Expr },
    Let { var : Var, val : Expr, res : Expr },
]

Var := Str implements [Eq, Hash]

Type : [
    Int,
    Lam { arg : Type, res : Type },
    TypeVar TypeVar,
]

TypeVar := U64 implements [Eq, Hash]

TypeEnv : Dict Expr Type

Substitutions : Dict Type Type

infer : TypeEnv, Expr -> (Substitutions, Type)
infer = \env, expr ->
    when expr is
        Int _ ->
            (Dict.empty {}, Int)

        Var var ->
            when Dict.get env expr is
                Ok type -> (Dict.empty {}, type)
                Err KeyNotFound -> crash "unknown var $(name var)"

        Lam { arg, body } ->
            argType = newTypeVar env
            (subs, bodyType) = infer (Dict.insert env (Var arg) argType) body
            (subs, Lam { arg: subType subs argType, res: bodyType })

        App { fn, arg } ->
            (subs1, fnType) = infer env fn
            (subs2, argType) = infer (subEnv subs1 env) arg
            resType = newTypeVar env
            subs3 = unify (subType subs2 fnType) (Lam { arg: argType, res: resType })
            subs = subs1 |> Dict.insertAll subs2 |> Dict.insertAll subs3
            (subs, subType subs3 resType)

        Let { var, val, res } ->
            varType = newTypeVar env
            (subs1, valType) = infer (Dict.insert env (Var var) varType) val
            subs2 = unify (subType subs1 varType) valType
            (subs3, resType) =
                Dict.insertAll subs2 subs1
                |> subEnv env
                |> Dict.insert (Var var) valType
                |> infer res
            subs = subs1 |> Dict.insertAll subs2 |> Dict.insertAll subs3
            (subs, resType)

newTypeVar : TypeEnv -> Type
newTypeVar = \env ->
    keepHighest = \n, var ->
        when var is
            Int -> n
            Lam _ -> n
            TypeVar (@TypeVar m) -> if n < m then m else n
    highest =
        Dict.values env
        |> List.walk 0 keepHighest

    TypeVar (@TypeVar (highest + 1))

name : Var -> Str
name = \@Var str -> str

printType : Type -> Str
printType = \type ->
    when type is
        Int -> "Int"
        Lam { arg, res } -> "$(printType arg) -> $(printType res)"
        TypeVar (@TypeVar n) -> "<typevar $(Num.toStr n)>"

subEnv : Substitutions, TypeEnv -> TypeEnv
subEnv = \subs, env ->
    Dict.map env \_, type -> subType subs type

subType : Substitutions, Type -> Type
subType = \subs, type ->
    when Dict.get subs type is
        Ok t -> t
        Err KeyNotFound -> type

unify : Type, Type -> Substitutions
unify = \t1, t2 ->
    when (t1, t2) is
        (x, y) if x == y ->
            Dict.empty {}

        (TypeVar _, y) ->
            Dict.single t1 y

        (x, TypeVar _) ->
            Dict.single t2 x

        (Lam x, Lam y) ->
            subs1 = unify x.arg y.arg
            subs2 = unify (subType subs1 x.res) (subType subs1 y.res)
            Dict.insertAll subs2 subs1

        _ ->
            crash "unify: Can't unify `$(printType t1)` with `$(printType t2)`"
