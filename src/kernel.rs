pub fn typecheck(items: Vec<Item>, reporter: &mut Reporter) {
    let mut variables = Vec::new();

    for item in items {
        match item {
            Item::Definition(item) => {
                let (type_type, r#type) = type_of(&mut variables, item.r#type, reporter);
                let TermKind::Sort { .. } = type_type.kind else {
                    reporter.error(r#type.span, "definition type is not a type");
                    // TODO: This offsets the other definitions :(
                    continue;
                };

                let body = item.body.map(|body| {
                    let (got_type, body) = type_of(&mut variables, body, reporter);
                    if got_type != r#type {
                        reporter.error(
                            body.span,
                            format!(
                                "type mismatch of definition:\n expected: {}\n      got: {}",
                                r#type.display(reporter.source()),
                                got_type.display(reporter.source()),
                            ),
                        );
                    }
                    body
                });
                variables.push((r#type, body));
            }
            Item::Inductive(mut item) => {
                // We follow Lean and don’t reduce anything here, even though we could.
                let TermKind::Sort { .. } = item.sort.kind else {
                    reporter.error(item.sort.span, "type is not a sort");
                    // TODO: This offsets the other definitions :(
                    continue;
                };

                // Bring the params in scope
                let params_len = item.params.len();
                for param in item.params {
                    let (mut param_type, mut param) = type_of(&mut variables, param, reporter);
                    if !matches!(param_type.kind, TermKind::Sort { .. }) {
                        reporter.error(param.span, "parameter is not a type");

                        // Guess that the user meant to write the _type_ of the term they wrote
                        // e.g. convert `inductive foo (x : 5)` to `inductive foo (x : nat)`
                        let assumed_type = Term {
                            kind: param_type.kind,
                            span: param.span,
                        };
                        (param_type, param) = type_of(&mut variables, assumed_type, reporter);
                        assert!(matches!(param_type.kind, TermKind::Sort { .. }));
                    }
                    variables.push((param, None));
                }
                // Bring the type itself in scope (with parameters applied)
                variables.push((item.sort, None));

                // Check each of the constructors
                let constructors = item
                    .constructors
                    .drain(..)
                    .map(|constructor| check_constructor(&mut variables, constructor, reporter))
                    .collect::<Vec<_>>();

                // Remove the type name and parameters from the scope
                let (sort, _) = variables.pop().unwrap();
                let params = variables
                    .drain(variables.len() - params_len..)
                    .map(|(param, _)| param)
                    .collect::<Vec<_>>();

                // For ownership reasons, we first make the recursor, then the constructors, then
                // the type former. Note that they are actually added to the global context in the
                // _reverse_ order of this.

                // Make the recursor. Local context looks like:
                //
                // Globals TypeFormer C₁…Cₙ P₁…Pₘ C p₁…pₙ p
                //
                // where:
                // - C₁…Cₙ are the constructors 1 to n (where n = constructors.len())
                // - P₁…Pₘ are the parameters 1 to m (where m = params.len())
                // - C is the motive
                // - p₁…pₙ are the minor premises from 1 to n (equal to the number of constructors)
                // - p is the major premise
                let motive_ref = var_term(Span::none(), constructors.len() + 1);
                let major_premise = var_term(Span::none(), 0);
                let mut recursor = app_term(Span::none(), motive_ref, major_premise);

                // The formed type, constructed as the type of the major premise. Start with
                // accessing the type former:
                //
                // Globals TypeFormer C₁…Cₙ P₁…Pₘ C p₁…pₙ p
                //                    \___/ \___/ V \___/
                //                      n  +  m + 1 + n    = 2 * n + m + 1
                let mut formed_type =
                    var_term(Span::none(), 2 * constructors.len() + params.len() + 1);
                for j in (0..params.len()).rev() {
                    // Access each parameter to apply to the type former:
                    //
                    // Globals TypeFormer C₁…Cₙ P₁…Pₘ C p₁…pₙ p
                    //                          \___/ V \___/
                    //                            j + 1 + n
                    let param = var_term(Span::none(), j + 1 + constructors.len());
                    formed_type = app_term(Span::none(), formed_type, param);
                }
                // TODO: Fix for `Prop`s
                recursor = pi_term(Span::none(), formed_type, recursor);

                // Add each minor premise. The local context looks slightly different:
                //
                // Globals TypeFormer C₁…Cₙ P₁…Pₘ C p₁…pᵢ A₁…Aₗ R₁…Rᵣ
                //
                // where:
                // - A₁…Aₗ are the constructor arguments from 1 to l
                //  (l = constructor.params.len())
                // - R₁…Rᵣ are the recursive arguments of each from 1 to r
                //  (r = constructor.recursive_params.len())
                //
                // To illustrate how recursors are generated, take this inductive type:
                //
                // inductive T (P₁ : Type) (P₂ : Type) :: Type
                // | C₁ : T
                // | C₂ : (δ₁ → T) → T
                // | C₃ : (δ₁ → T) → ℕ → (δ₁ → δ₂ → T) → T
                //
                // The following recursor is generated:
                //
                // Π P₁ : Type,
                // Π P₂ : Type,
                // Π motive : T P₁…Pₙ → Sort u_1,
                // Π p₁ : motive (C₁ P₁…Pₙ),
                // Π p₂ : Π a₁ : δ₁ → T P₁…Pₙ,
                //        Π r₁ : Π d₁ : δ₁, motive (a₁ d₁),
                //        motive (T.C₂ P₁…Pₙ a₁),
                // Π p₃ : Π a₁ : δ₁ → T P₁…Pₙ,
                //        Π a₂ : ℕ,
                //        Π a₃ : δ₁ → δ₂ → T P₁…Pₙ,
                //        Π r₁ : Π d₁ : δ₁, motive (a₁ d₁),
                //        Π r₂ : Π d₁ : δ₁, Π d₂ : δ₂, motive (a₃ d₁ d₂),
                //        motive (T.C₃ P₁…Pₙ a₁ a₂ a₃),
                // Π p : T P₁…Pₙ,
                // motive p
                for (i, constructor) in constructors.iter().enumerate().rev() {
                    // The total number of parameters to this minor premise (= l + r).
                    let minor_params =
                        constructor.params.len() + constructor.recursive_params.len();

                    // This constructor with all its parameters and constructor parameters applied.
                    //
                    // Globals TypeFormer C₁…Cₙ P₁…Pₘ C p₁…pᵢ A₁…Aₗ R₁…Rᵣ
                    //                      \_/ \___/ V \___/ \___/ \___/
                    //                  (n−1-i)+  n + 1 + i  +  l  +  r = 2n + l + r
                    let constructor_index = 2 * params.len() + minor_params;
                    let mut applied = var_term(Span::none(), constructor_index);
                    // Apply the parameters.
                    for j in (0..params.len()).rev() {
                        // Globals TypeFormer C₁…Cₙ P₁…Pₘ C p₁…pᵢ A₁…Aₗ R₁…Rᵣ
                        //                          \___/ V \___/ \___/ \___/
                        //                            j + 1 + i  +  l  +  r
                        let param = var_term(Span::none(), j + 1 + i + minor_params);
                        applied = app_term(Span::none(), applied, param);
                    }
                    // Apply the constructor parameters.
                    for j in (0..constructor.params.len()).rev() {
                        // Globals TypeFormer C₁…Cₙ P₁…Pₘ C p₁…pᵢ A₁…Aₗ R₁…Rᵣ
                        //                                        \___/ \___/
                        //                                          j  +  r
                        let param = var_term(Span::none(), j + constructor.recursive_params.len());
                        applied = app_term(Span::none(), applied, param);
                    }

                    let mut minor_premise = applied;

                    // Construct parameters to the minor premise for each recursive parameter.
                    for (t, &(j, param_params)) in
                        constructor.recursive_params.iter().enumerate().rev()
                    {
                        let mut param_type = constructor.params[j].clone();

                        // Adjust the parameter type for the new context.
                        // Old context: Globals                  P₁…Pₘ  Type   A₁…Aⱼ
                        // New context: Globals TypeFormer C₁…Cₙ P₁…Pₘ C p₁…pᵢ A₁…Aₗ R₁…Rₜ
                        param_type.with_free(|v| {
                            // If `v` is referencing a previous constructor parameter, offset it,
                            // taking into account that it used to have fewer constructor
                            // parameters and no recursive parameters in scope.
                            //
                            // Globals TypeFormer C₁…Cₙ P₁…Pₘ C p₁…pᵢ A₁…Aₗ R₁…Rₜ
                            //                                        \___/ \___/
                            //                                        l − j + t
                            let Some(v) = v.checked_sub(j) else {
                                let v = v + constructor.params.len() - j + t;
                                return TermKind::Variable(Variable(v));
                            };
                            // If `v` is referencing the type itself, we substitute in our motive
                            // applied for this constructor parameter.
                            let Some(v) = v.checked_sub(1) else {
                                // Retrieve the corresponding constructor parameter.
                                //
                                // Globals TypeFormer C₁…Cₙ P₁…Pₘ C p₁…pᵢ A₁…Aₗ R₁…Rₜ
                                //                                         \__/ \___/
                                //                                        l−1−j + t
                                let param_v = constructor.params.len() - 1 - j + t;
                                let mut param = var_term(Span::none(), param_v);

                                // Applies to the constructor parameter each value.
                                for k in (0..param_params).rev() {
                                    let param_param = var_term(Span::none(), k);
                                    param = app_term(Span::none(), param, param_param);
                                }

                                // Retrieve the motive.
                                //
                                // Globals TypeFormer C₁…Cₙ P₁…Pₘ C p₁…pᵢ A₁…Aₗ R₁…Rₜ
                                //                                  \___/ \___/ \___/
                                //                                    i  +  l   + t
                                let motive_v = i + constructor.params.len() + t;

                                // Apply the applied constructor parameter to the motive.
                                return TermKind::Application {
                                    left: Box::new(var_term(Span::none(), motive_v)),
                                    right: Box::new(param),
                                };
                            };
                            // If `v` is referencing a previous parameter, offset it by everything
                            // we have added to the local context:
                            //
                            // Globals TypeFormer C₁…Cₙ P₁…Pₘ C p₁…pᵢ A₁…Aₗ R₁…Rₜ
                            //                                V \___/ \___/ \___/
                            //                                1 + i  +  l  +  t
                            let Some(v) = v.checked_sub(params.len()) else {
                                let v = v + 1 + i + constructor.params.len() + t;
                                return TermKind::Variable(Variable(v));
                            };
                            // Otherwise, `v` is referencing something in the global scope.
                            //
                            // Globals TypeFormer C₁…Cₙ P₁…Pₘ C p₁…pᵢ A₁…Aₗ R₁…Rₜ
                            //         \________/ \___/ \___/ V \___/ \___/ \___/
                            //             1     +  n  +  m + 1 + i  +  l  +  t
                            let v = v
                                + 1
                                + constructors.len()
                                + params.len()
                                + 1
                                + i
                                + constructor.params.len()
                                + t;
                            TermKind::Variable(Variable(v))
                        });

                        minor_premise = pi_term(Span::none(), param_type, minor_premise);
                    }

                    // Construct parameters to the minor premise for each parameter, both recursive
                    // and non-recursive.
                    for (j, param_type) in constructor.params.iter().enumerate().rev() {
                        let mut param_type = param_type.clone();

                        // Adjust the parameter type for the new context.
                        // Old context: Globals                  P₁…Pₘ  Type   A₁…Aⱼ
                        // New context: Globals TypeFormer C₁…Cₙ P₁…Pₘ C p₁…pᵢ A₁…Aⱼ
                        param_type.with_free(|v| {
                            // If `v` is referencing a previous constructor parameter, it can stay
                            // the same.
                            let Some(v) = v.checked_sub(j) else {
                                return TermKind::Variable(Variable(v));
                            };
                            // If `v` is referencing the type itself, we substitute in the type
                            // former with all parameters applied.
                            let Some(v) = v.checked_sub(1) else {
                                // Globals TypeFormer C₁…Cₙ P₁…Pₘ C p₁…pᵢ A₁…Aⱼ
                                //                    \___/ \___/ V \___/ \___/
                                //                      n  +  m + 1 + i  +  j
                                let formed_type_v = constructors.len() + params.len() + 1 + i + j;
                                let mut formed_type = var_term(Span::none(), formed_type_v);

                                // Apply all the parameters.
                                for k in (0..params.len()).rev() {
                                    // Globals TypeFormer C₁…Cₙ P₁…Pₘ C p₁…pᵢ A₁…Aⱼ
                                    //                           \__/ V \___/ \___/
                                    //                            k + 1 + i  +  j
                                    let v = var_term(Span::none(), k + 1 + i + j);
                                    formed_type = app_term(Span::none(), formed_type, v);
                                }
                                return formed_type.kind;
                            };
                            // If `v` is referencing a previous parameter, offset it by everything
                            // we have added to the local context:
                            //
                            // Globals TypeFormer C₁…Cₙ P₁…Pₘ C p₁…pᵢ A₁…Aⱼ
                            //                                V \___/ \___/
                            //                                1 + i  +  j
                            let Some(v) = v.checked_sub(params.len()) else {
                                return TermKind::Variable(Variable(v + 1 + i + j));
                            };
                            // Otherwise, `v` is referencing something in the global scope.
                            //
                            // Globals TypeFormer C₁…Cₙ P₁…Pₘ C p₁…pᵢ A₁…Aⱼ
                            //         \________/ \___/ \___/ V \___/ \___/
                            //             1     +  n  +  m + 1 + i  +  j
                            let v = v + 1 + constructors.len() + params.len() + 1 + i + j;
                            TermKind::Variable(Variable(v))
                        });

                        minor_premise = pi_term(Span::none(), param_type, minor_premise);
                    }

                    recursor = pi_term(Span::none(), minor_premise, recursor);
                }

                // Add the motive parameter to the recursor.
                {
                    // The formed type: the type former with all parameters applied. local context:
                    //
                    // Globals TypeFormer C₁…Cₙ P₁…Pₘ
                    //                    \___/ \___/
                    //                      n  +  m
                    let type_former = constructors.len() + params.len();
                    let mut formed_type = var_term(Span::none(), type_former);
                    for i in (0..params.len()).rev() {
                        let param = var_term(Span::none(), i);
                        formed_type = app_term(Span::none(), formed_type, param);
                    }

                    // TODO: Universe genericity
                    let level = lit_universe_level(Span::none(), 1);
                    let result = sort_term(Span::none(), level);

                    let motive_type = pi_term(Span::none(), formed_type, result);

                    recursor = pi_term(Span::none(), motive_type, recursor);
                }

                // Add the parameters to the recursor.
                for (i, param) in params.iter().enumerate().rev() {
                    let mut param = param.clone();
                    // Take into account the type former and constructors that are now in scope
                    // but weren’t when variable resolution occured.
                    // Old context: Globals                  P₁…Pᵢ
                    // New context: Globals TypeFormer C₁…Cₙ P₁…Pᵢ
                    //                      \________/ \___/ \___/
                    //                          1     +  n  ,  i
                    param.with_free(|v| {
                        let v = if v < i { v } else { v + 1 + constructors.len() };
                        TermKind::Variable(Variable(v))
                    });
                    recursor = pi_term(Span::none(), param, recursor);
                }

                // Make each of the constructors; don’t add to `variables` just yet because we
                // haven’t added the type former yet. When forming each constructor, local context
                // looks like:
                //
                // Globals TypeFormer C₁…Cᵢ P₁…Pₙ (constructor parameters)
                //
                // where:
                // - C₁…Cᵢ are the constructors 1 to i
                // - P₁…Pₙ are the parameters 1 to n
                //
                // Also reuse the `item.constructors` vector since we have it lying around.
                let mut constructor_types = item.constructors;
                for (i, constructor) in constructors.into_iter().enumerate() {
                    let output_span = constructor.output_span;

                    // Reconstruct the original constructor type term for easier processing. We use
                    // the original local context to find the index of the type:
                    //
                    // Globals P₁…Pₙ Type A₁…Aₗ
                    //                    \___/
                    //                      l
                    let mut term = var_term(output_span, constructor.params.len());
                    for param in constructor.params.into_iter().rev() {
                        term = pi_term(param.span.join(term.span), param, term);
                    }

                    // The formed type is initially the type former (whose index is offset by all
                    // the parameters and the number of constructors generated so far).
                    //
                    // We construct it in the local context excluding the constructor parameters,
                    // as it will be offset appropriately by the below `with_free` call:
                    //
                    // Globals TypeFormer C₁…Cᵢ P₁…Pₙ
                    //                    \___/ \___/
                    //                      i  +  n
                    let mut formed_type = var_term(output_span, i + params.len());
                    // Then we apply each parameter
                    for j in (0..params.len()).rev() {
                        formed_type = app_term(output_span, formed_type, var_term(Span::none(), j));
                    }

                    // Replace the `constructor`’s type variables with the fully formed type.
                    // Old context: Globals                  P₁…Pₙ Type
                    // New context: Globals TypeFormer C₁…Cᵢ P₁…Pₙ
                    term.with_free(|v| {
                        // When v = 0, substitute in the fully formed type.
                        let Some(v) = v.checked_sub(1) else {
                            return formed_type.kind.clone();
                        };
                        // If `v` refers to a parameter, remove its offset.
                        let Some(v) = v.checked_sub(params.len()) else {
                            return TermKind::Variable(Variable(v));
                        };
                        // Otherwise, `v` refers to a global, so offset it by the type former, the
                        // constructors and the parameters.
                        TermKind::Variable(Variable(v + 1 + i + params.len()))
                    });

                    // Add on all the parameters to the constructor
                    for (j, param) in params.iter().enumerate().rev() {
                        let mut param = param.clone();
                        // Take into account the type former and constructors that are now in scope
                        // but weren’t when variable resolution occured.
                        // Old context: Globals                  P₁…Pⱼ
                        // New context: Globals TypeFormer C₁…Cᵢ P₁…Pⱼ
                        //                      \________/ \___/ \___/
                        //                          1     +  i  ,  j
                        param.with_free(|v| {
                            TermKind::Variable(Variable(if v < j { v } else { v + i + 1 }))
                        });
                        term = pi_term(constructor.span, param, term);
                    }

                    constructor_types.push(term);
                }

                // Construct the type former, then add it to the global scope
                let mut type_former = sort;
                for param in params.into_iter().rev() {
                    let span = param.span.join(type_former.span);
                    // No variable offsetting is necessary as:
                    // Old context: Globals P₁…Pᵢ
                    // New context: Globals P₁…Pᵢ
                    type_former = pi_term(span, param, type_former);
                }
                variables.push((type_former, None));

                // Add the constructors & recursor to the global scope
                for constructor in constructor_types {
                    variables.push((constructor, None));
                }
                variables.push((recursor, None));
            }
        }
    }
}

struct Constructor {
    // Local context of each param, whether recursive or not:
    //
    // Globals P₁…Pₙ Type
    params: Vec<Term>,
    /// Indices of parameters that are recursive. Also contains the number of parameters this
    /// recursive parameter takes itself.
    recursive_params: Vec<(usize, usize)>,
    span: Span,
    output_span: Span,
}

/// Checks, typechecks and reduces a constructor.
// Copy Lean: don’t reduce the outer term, but reduce inner terms
// TODO: Disallow depending on recursive args
// TODO: Move to &mut-based API
fn check_constructor(
    variables: &mut Vec<(Term, Option<Term>)>,
    mut term: Term,
    reporter: &mut Reporter,
) -> Constructor {
    let span = term.span;
    let mut params = 0;
    let mut recursive_params = Vec::new();
    loop {
        // This variable holds what the current value of `term` sees as the type that is being
        // constructed. As the local context of each constructor places the type variable last thing
        // before the constructor params, we don’t have to offset this value beyond the number of
        // constructor parameters we have encountered.
        let type_constructed = Variable(params);

        match term.kind {
            // TODO: inductive family-ify
            TermKind::Variable(v) if v == type_constructed => break,
            TermKind::Abstraction {
                token: AbstractionToken::Pi,
                variable: _,
                r#type,
                body,
            } => {
                let (_, r#type) = type_of(variables, *r#type, reporter);
                let (recursive, num_params) =
                    check_strictly_positive(&r#type, type_constructed, reporter);
                if recursive {
                    recursive_params.push((params, num_params));
                }
                variables.push((r#type, None));
                params += 1;
                term = *body;
            }
            TermKind::Sort { .. }
            | TermKind::Variable(_)
            | TermKind::Abstraction { .. }
            | TermKind::Application { .. } => {
                reporter.error(term.span, "invalid return type");
                break;
            }
            TermKind::Error => break,
        }
    }
    Constructor {
        params: variables
            .drain(variables.len() - params..)
            .map(|(p, _)| p)
            .collect(),
        recursive_params,
        span,
        output_span: term.span,
    }
}

/// Asserts that the appearance of `variable` in the given term is strictly positive. Returns
/// whether the term is recursive or not, and the number of parameters it takes.
///
/// See <https://counterexamples.org/strict-positivity.html> for why this check is necessary.
fn check_strictly_positive(
    mut term: &Term,
    variable: Variable,
    reporter: &mut Reporter,
) -> (bool, usize) {
    let mut params = 0;
    let recursive = loop {
        match &term.kind {
            // TODO: inductive family-ify
            TermKind::Variable(v) if v.0 == variable.0 + params => break true,
            TermKind::Sort { .. } | TermKind::Variable(_) => break false,
            TermKind::Abstraction {
                token: AbstractionToken::Pi,
                variable: _,
                r#type,
                body,
            } => {
                check_not_contained(r#type, variable, reporter);
                term = body;
                params += 1;
            }
            TermKind::Abstraction { .. } | TermKind::Application { .. } => {
                check_not_contained(term, variable, reporter);
                break false;
            }
            TermKind::Error => break false,
        }
    };
    (recursive, params)
}

fn check_not_contained(term: &Term, variable: Variable, reporter: &mut Reporter) {
    let mut to_check = vec![(term, variable)];
    while let Some((term, variable)) = to_check.pop() {
        match &term.kind {
            TermKind::Variable(v) if *v == variable => {
                reporter.error(
                    term.span,
                    "non-positive occurence of datatype being declared",
                );
            }
            TermKind::Abstraction { r#type, body, .. } => {
                to_check.push((r#type, variable));
                to_check.push((body, Variable(variable.0 + 1)));
            }
            TermKind::Application { left, right } => {
                to_check.push((left, variable));
                to_check.push((right, variable));
            }
            TermKind::Error | TermKind::Variable(_) | TermKind::Sort { .. } => {}
        }
    }
}

fn type_of(
    variables: &mut Vec<(Term, Option<Term>)>,
    mut term: Term,
    reporter: &mut Reporter,
) -> (Term, Term) {
    let r#type: Term;

    match term.kind {
        TermKind::Sort { level } => {
            let level = reduce_universe_level(&level, reporter);

            let raised_level = UniverseLevel {
                kind: UniverseLevelKind::Addition {
                    left: Box::new(level.clone()),
                    right: Some(UniverseLevelLit {
                        value: 1,
                        span: level.span,
                    }),
                },
                span: level.span,
            };
            r#type = Term {
                kind: TermKind::Sort {
                    level: reduce_universe_level(&raised_level, reporter),
                },
                span: Span::none(),
            };

            term.kind = TermKind::Sort { level };
        }
        TermKind::Variable(v) => {
            let pull_by = v.0 + 1;
            let (mut type_term, value) = variables[variables.len() - pull_by].clone();
            type_term.increase_free(pull_by);
            r#type = Term {
                kind: type_term.kind,
                span: type_term.span,
            };
            // TODO: Is this enough to δ-reduce?
            if let Some(mut value) = value {
                value.increase_free(pull_by);
                term = value;
            }
        }
        TermKind::Abstraction {
            token,
            variable,
            r#type: param_type,
            body,
        } => {
            let (mut param_type_type, mut param_type) = type_of(variables, *param_type, reporter);

            let param_level = match param_type_type.kind {
                TermKind::Sort { level } => level,
                kind => {
                    reporter.error(
                        param_type.span,
                        format_args!("{token} parameter is not a type"),
                    );

                    // Guess that the user meant to write the _type_ of the term they wrote
                    // e.g. convert (λ x : 5, x) to (λ x : nat, x)
                    let assumed_type = Term {
                        kind,
                        span: param_type.span,
                    };
                    (param_type_type, param_type) = type_of(variables, assumed_type, reporter);
                    let TermKind::Sort { level } = param_type_type.kind else { unreachable!() };
                    level
                }
            };

            variables.push((param_type, None));
            let (mut body_type, mut body) = type_of(variables, *body, reporter);
            let param_type = Box::new(variables.pop().unwrap().0);

            match token {
                // The type of the Π type is Sort imax u v
                AbstractionToken::Pi => {
                    let body_level = match body_type.kind {
                        TermKind::Sort { level } => level,
                        kind => {
                            reporter.error(body.span, "Π body is not a type");

                            // Guess that the user meant to write the _type_ of the term they wrote.
                            // e.g. convert (Π x : nat, 6) to (Π x : nat, nat)
                            let assumed_type = Term {
                                kind,
                                span: body.span,
                            };
                            (body_type, body) = type_of(variables, assumed_type, reporter);
                            let TermKind::Sort { level } = body_type.kind else { unreachable!() };
                            level
                        }
                    };

                    let level = UniverseLevel {
                        kind: UniverseLevelKind::Max {
                            i: true,
                            left: Box::new(param_level),
                            right: Box::new(body_level),
                        },
                        span: Span::none(),
                    };

                    r#type = Term {
                        kind: TermKind::Sort {
                            level: reduce_universe_level(&level, reporter),
                        },
                        span: Span::none(),
                    };
                }
                // The type of the λ type is the Π type
                AbstractionToken::Lambda => {
                    r#type = Term {
                        kind: TermKind::Abstraction {
                            token: AbstractionToken::Pi,
                            variable,
                            r#type: param_type.clone(),
                            // TODO: Are the de bruijn indices correct here?
                            body: Box::new(body_type),
                        },
                        span: Span::none(),
                    };
                }
            }

            term.kind = TermKind::Abstraction {
                token,
                variable,
                r#type: param_type,
                body: Box::new(body),
            };
        }
        // β-reduction
        TermKind::Application { left, right } => {
            let (left_type, left) = type_of(variables, *left, reporter);
            let (right_type, right) = type_of(variables, *right, reporter);

            let TermKind::Abstraction { token: AbstractionToken::Pi, variable: _, r#type: param_type, body: mut ret_type } = left_type.kind else {
                reporter.error(left.span, "left hand side of application is not a function");
                // Recover by ignoring the application
                return (left_type, left);
            };

            if *param_type != right_type {
                reporter.error(
                    right.span,
                    format!(
                        "function application type mismatch on {} of {}\n expected: {}\n      got: {}",
                        left.display(reporter.source()),
                        right.display(reporter.source()),
                        param_type.display(reporter.source()),
                        right_type.display(reporter.source()),
                    ),
                );
            }

            // Replace the lowest free variable in the return type with the new type.
            ret_type.replace(&right);
            (_, r#type) = type_of(variables, *ret_type, reporter);

            // TODO: recursive replacing; is this right?
            if let TermKind::Abstraction {
                token: AbstractionToken::Lambda,
                variable: _,
                r#type,
                mut body,
            } = left.kind
            {
                assert!(*r#type == *param_type);
                // Replace the lowest free variable in the lambda body with the new value.
                body.replace(&right);
                (_, term) = type_of(variables, *body, reporter);
            } else {
                let left = Box::new(left);
                let right = Box::new(right);
                term.kind = TermKind::Application { left, right };
            };
        }
        TermKind::Error => {
            r#type = Term {
                kind: TermKind::Error,
                span: Span::none(),
            }
        }
    }

    (r#type, term)
}

fn reduce_universe_level(level: &UniverseLevel, reporter: &mut Reporter) -> UniverseLevel {
    let kind = match &level.kind {
        UniverseLevelKind::Lit(n) => UniverseLevelKind::Lit(*n),
        UniverseLevelKind::Variable(v) => match *v {},
        UniverseLevelKind::Addition {
            left,
            right: Some(right),
        } => {
            match reduce_universe_level(left, reporter).kind {
                UniverseLevelKind::Lit(left) => {
                    let lit = add_universe_level_lit(left, *right, reporter);
                    UniverseLevelKind::Lit(lit)
                }
                UniverseLevelKind::Variable(v) => match v {},
                UniverseLevelKind::Addition {
                    left,
                    right: Some(right_2),
                } => {
                    let right = Some(add_universe_level_lit(*right, right_2, reporter));
                    UniverseLevelKind::Addition { left, right }
                }
                UniverseLevelKind::Max { .. } => todo!(),
                // Propagate the errors
                UniverseLevelKind::Error
                | UniverseLevelKind::Addition {
                    left: _,
                    right: None,
                } => UniverseLevelKind::Error,
            }
        }
        // Propagate the errors
        UniverseLevelKind::Addition {
            left: _,
            right: None,
        } => UniverseLevelKind::Error,
        UniverseLevelKind::Max { i, left, right } => {
            let left = reduce_universe_level(left, reporter);
            let right = reduce_universe_level(right, reporter);
            match (left.kind, right.kind) {
                (
                    UniverseLevelKind::Lit(_),
                    lit @ UniverseLevelKind::Lit(UniverseLevelLit { value: 0, .. }),
                ) if *i => lit,
                (UniverseLevelKind::Lit(left), UniverseLevelKind::Lit(right)) => {
                    UniverseLevelKind::Lit(UniverseLevelLit {
                        value: u32::max(left.value, right.value),
                        span: left.span.join(right.span),
                    })
                }
                _ => todo!(),
            }
        }
        UniverseLevelKind::Error => UniverseLevelKind::Error,
    };
    let span = level.span;
    UniverseLevel { kind, span }
}

fn add_universe_level_lit(
    left: UniverseLevelLit,
    right: UniverseLevelLit,
    reporter: &mut Reporter,
) -> UniverseLevelLit {
    let span = left.span.join(right.span);
    let value = left.value.checked_add(right.value).unwrap_or_else(|| {
        reporter.error(span, "universe too large");
        u32::MAX
    });
    UniverseLevelLit { value, span }
}

fn lit_universe_level(span: Span, value: u32) -> UniverseLevel {
    UniverseLevel {
        kind: UniverseLevelKind::Lit(UniverseLevelLit { value, span }),
        span,
    }
}

fn sort_term(span: Span, level: UniverseLevel) -> Term {
    Term {
        span,
        kind: TermKind::Sort { level },
    }
}

fn app_term(span: Span, left: Term, right: Term) -> Term {
    Term {
        span,
        kind: TermKind::Application {
            left: Box::new(left),
            right: Box::new(right),
        },
    }
}

fn var_term(span: Span, i: usize) -> Term {
    Term {
        span,
        kind: TermKind::Variable(Variable(i)),
    }
}

fn pi_term(span: Span, r#type: Term, body: Term) -> Term {
    Term {
        span,
        kind: TermKind::Abstraction {
            token: AbstractionToken::Pi,
            r#type: Box::new(r#type),
            body: Box::new(body),
            variable: Span::none(),
        },
    }
}

use crate::parser::AbstractionToken;
use crate::parser::UniverseLevelLit;
use crate::reporter::Reporter;
use crate::reporter::Span;
use crate::variables::Item;
use crate::variables::Term;
use crate::variables::TermKind;
use crate::variables::UniverseLevel;
use crate::variables::UniverseLevelKind;
use crate::variables::Variable;
