/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.builder;

import edu.kit.iti.algover.SymbexStateToFormula;
import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.FunctionSymbolFamily;
import edu.kit.iti.algover.term.FunctionSymbolFamily.InstantiatedFunctionSymbol;
import edu.kit.iti.algover.term.LetTerm;
import edu.kit.iti.algover.term.QuantTerm;
import edu.kit.iti.algover.term.QuantTerm.Quantifier;
import edu.kit.iti.algover.term.SchemaCaptureTerm;
import edu.kit.iti.algover.term.SchemaOccurTerm;
import edu.kit.iti.algover.term.SchemaTerm;
import edu.kit.iti.algover.term.SchemaVarTerm;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.VariableTerm;
import edu.kit.iti.algover.util.ASTUtil;
import edu.kit.iti.algover.util.BiFunctionWithException;
import edu.kit.iti.algover.util.FunctionWithException;
import edu.kit.iti.algover.util.HistoryMap;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.Pair;
import nonnull.NonNull;
import org.antlr.runtime.CommonToken;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.BiFunction;

/**
 * The Class TreeTermTranslator is used to create a {@link Term} object from a
 * {@link DafnyTree}. It supports schematic term entities.
 *
 * @see Term
 * @see DafnyTree
 *
 * @author Mattias Ulbrich
 */
public class TreeTermTranslator {

    /**
     * The Constant HEAP_VAR is the variable used for for heap assignments.
     */
    private static final VariableTerm HEAP_VAR =
            new VariableTerm("$heap", Sort.HEAP);

    /**
     * The symbol table from which the function symbols etc are to be taken.
     */
    private final SymbolTable symbolTable;

    /**
     * All bound variables are stored here during parsing.
     *
     * Invariant: Is empty as soon as parsing method returns.
     */
    private final HistoryMap<String, VariableTerm> boundVars =
            new HistoryMap<>(new HashMap<>());

    /**
     * The helper object to be used for term construction.
     */
    private final TermBuilder tb;

    /**
     * This map is used to construct a map for all terms to their original
     * DafnyTrees.
     */
    private final Map<Term, DafnyTree> referenceMap = new IdentityHashMap<>();

    /**
     * Instantiates a new term translator.
     *
     * If needed, the presented symbol table may be extended!
     *
     * @param symbolTable
     *            non-<code>null</code> symbol table for lookup of symbols.
     */
    public TreeTermTranslator(SymbolTable symbolTable) {
        assert symbolTable != null;
        this.symbolTable = symbolTable;
        this.tb = new TermBuilder(symbolTable);
    }


//    /**
//     * Builds a let-cascaded term for a tree and a variable map.
//     *
//     * All assignments in {@code map} are translated to cascading
//     * {@link LetTerm}s. The {@code expression} is then embedded into the
//     * cascade
//     *
//     * @param history
//     *            the non-<code>null</code> list of observed assignments
//     * @param expression
//     *            the expression to be translated
//     * @return the term which represents the let-cascade
//     * @throws TermBuildException
//     *             if terms in the tree are not well-formed.
//     */
//    private Term build(ImmutableList<DafnyTree> history, DafnyTree expression)
//            throws TermBuildException {
//        return buildLetCascade(history.reverse(), expression);
//    }
//
//    private Term buildLetCascade(ImmutableList<DafnyTree> history, DafnyTree expression)
//            throws TermBuildException {
//        if (history.size() == 0) {
//            return build(expression);
//        } else {
//            return buildLetExpression(history.getLast(),
//                    history.getTail(), expression);
//        }
//    }
//
//    /*
//     * see #buildLetCascade
//     */
//    private Term buildLetExpression(DafnyTree assignment, ImmutableList<DafnyTree> tail, DafnyTree result)
//            throws TermBuildException {
//        DafnyTree errorTree = assignment;
//
//        assert assignment.getType() == DafnyParser.ASSIGN;
//
//        try {
//            DafnyTree receiver = assignment.getChild(0);
//            DafnyTree expression = assignment.getChild(1);
//            LetTerm let;
//            switch (receiver.getType()) {
//            case DafnyParser.ID:
//                DafnyTree ref = receiver.getDeclarationReference();
//                if (ref.getType() != DafnyParser.FIELD) {
//                    String name = receiver.getText();
//                    Term assigned = build(expression);
//                    VariableTerm f = new VariableTerm(name, assigned.getSort());
//                    boundVars.put(name, f);
//                    let = new LetTerm(f, assigned, buildLetCascade(tail, result));
//                    boundVars.pop();
//                    return let;
//                } else {
//                    Term self = tb.self();
//                    Term field = tb.makeFieldConst(
//                            ref.getParent().getChild(0).getText(),
//                            ref.getChild(0).getText());
//                    Term value = build(expression);
//                    Term appl = tb.storeField(getHeap(), self, field, value);
//                    boundVars.put(HEAP_VAR.getName(), HEAP_VAR);
//                    let = new LetTerm(HEAP_VAR, appl, buildLetCascade(tail, result));
//                    boundVars.pop();
//                    return let;
//                }
//
//            case DafnyParser.FIELD_ACCESS: {
//                Term object = build(receiver.getChild(0));
//                Term field = tb.makeFieldConst(object.getSort().toString(),
//                        receiver.getChild(1).getText());
//                Term value = build(expression);
//
//                Term appl = tb.storeField(getHeap(), object, field, value);
//                boundVars.put(HEAP_VAR.getName(), HEAP_VAR);
//                let = new LetTerm(HEAP_VAR, appl, buildLetCascade(tail, result));
//                boundVars.pop();
//                return let;
//            }
//
//            case DafnyParser.ARRAY_ACCESS: {
//                // TODO only for 1-dim at the moment
//                Term object = build(receiver.getChild(0));
//                Term index = build(receiver.getChild(1));
//                Term value = build(expression);
//                if (object.getSort().getName().equals("array")) {
//                    Term heap = getHeap();
//                    Term appl = tb.storeArray(heap, object, index, value);
//                    boundVars.put(HEAP_VAR.getName(), HEAP_VAR);
//                    let = new LetTerm(HEAP_VAR, appl, buildLetCascade(tail, result));
//                    boundVars.pop();
//                    return let;
//                } else if (object.getSort().getName().equals("seq")) {
//                    DafnyTree call = ASTUtil.call("$seq_upd<int>", receiver.getChild(0),
//                            receiver.getChild(1), expression);
//                    DafnyTree assign = ASTUtil.assign(receiver.getChild(0), call);
//                    return buildLetExpression(assign, tail, result);
//                }
//            }
//
//            //            case DafnyParser.LISTEX:
//            //                // TODO: In a later revision make this seq<?> or similar.
//            //                List<Pair<FunctionSymbol, Term>> updates = new ArrayList<>();
//            //                for (int i = 0; i < assignment.getChildCount(); i++) {
//            //                    f = symbolTable.getFunctionSymbol(var + "_" + i);
//            //                    if (f == null) {
//            //                        f = new FunctionSymbol(var + "_" + i, Sort.INT);
//            //                        symbolTable.addFunctionSymbol(f);
//            //                    }
//            //                    updates.add(new Pair<>(f, build(assignment.getChild(i))));
//            //                }
//            //                return new LetTerm(updates, result);
//
//            default:
//                throw new Error("Unsupported assignment type: " + receiver.getType());
//            }
//        } catch (TermBuildException ex) {
//            if (!ex.hasLocation()) {
//                ex.setLocation(errorTree);
//            }
//            throw ex;
//        }
//    }

    private Term getHeap() throws TermBuildException {
        // This is naive since someone might call their variable "heap" manually.
        // Mitigated sind "$heap" is now protected by $.
        VariableTerm bound = boundVars.get(HEAP_VAR.getName());
        if(bound != null) {
            return bound;
        } else {
            return tb.heap();
        }
    }

    /**
     * Builds a term for a dafny tree.
     *
     * @param tree the non-<code>null</code> tree object standing for the term
     * @return the term representing the tree
     * @throws TermBuildException if the term is not well-formed
     */
    public Term build(DafnyTree tree) throws TermBuildException {

        Term result;

        switch (tree.getType()) {
        case DafnyParser.AND:
            result = buildBinary(BuiltinSymbols.AND, tree);
            break;

        case DafnyParser.OR:
            result = buildBinary(BuiltinSymbols.OR, tree);
            break;

        case DafnyParser.IMPLIES:
            result = buildBinary(BuiltinSymbols.IMP, tree);
            break;

        case DafnyParser.GE:
            result = buildBinary(BuiltinSymbols.GE, tree);
            break;

        case DafnyParser.GT:
            result = buildBinary(BuiltinSymbols.GT, tree);
            break;

        case DafnyParser.LE:
            result = buildBinary(BuiltinSymbols.LE, tree);
            break;

        case DafnyParser.LT:
            result = buildBinary(BuiltinSymbols.LT, tree);
            break;

        case DafnyParser.PLUS:
            result = buildBinary(
                symmetricBinarySymbol(sort -> {
                switch(sort.getName()) {
                case "int":
                    return BuiltinSymbols.PLUS;
                case "set":
                    return BuiltinSymbols.UNION.instantiate(sort.getArgument(0));
                case "seq":
                    return BuiltinSymbols.SEQ_CONCAT.instantiate(sort.getArgument(0));
                case "multiset":
                    // TODO
                    throw new Error("IMPLEMENT ME!");
                default:
                    throw new TermBuildException("'+' is not supported for sort " + sort);
                }
            }), tree);
            break;

        case DafnyParser.MINUS:
            if (tree.getChildCount() == 1) {
                result = buildUnary(BuiltinSymbols.NEG, tree);
            } else {
                result = buildBinary(BuiltinSymbols.MINUS, tree);
            }
            break;

        case DafnyParser.TIMES:
            result = buildBinary(symmetricBinarySymbol(sort -> {
                switch(sort.getName()) {
                case "int":
                    return BuiltinSymbols.TIMES;
                case "set":
                    return BuiltinSymbols.INTERSECT.instantiate(sort.getArgument(0));
                case "multiset":
                    // TODO
                    throw new Error("IMPLEMENT ME!");
                default:
                    throw new TermBuildException("'*' is not supported for these arguments");
                }
            }), tree);
            break;

        case DafnyParser.IN:
            result = buildBinary((x,y) -> {
                switch(y.getSort().getName()) {
                case "set":
                    return BuiltinSymbols.SET_IN.instantiate(y.getSort().getArgument(0));
                default:
                    throw new Error("Not yet implemented");
                }
            }, tree);
            break;

        case DafnyParser.NOT:
            result = buildUnary(BuiltinSymbols.NOT, tree);
            break;

        case DafnyParser.EQ:
            result = buildBinary(symmetricBinarySymbol(sort -> BuiltinSymbols.EQ.instantiate(sort)), tree);
            break;

        case DafnyParser.NEQ:
            result = buildBinary(symmetricBinarySymbol(sort -> BuiltinSymbols.EQ.instantiate(sort)), tree);
            result = tb.negate(result);
            break;

        case DafnyParser.LOGIC_ID:
        case DafnyParser.ID:
        case DafnyParser.TRUE:
        case DafnyParser.FALSE:
        case DafnyParser.THIS:
        case DafnyParser.INT_LIT:
            result = buildIdentifier(tree);
            break;

        case DafnyParser.NULL:
            result = buildNull(tree);
            break;

        case DafnyParser.SETEX:
            result = buildSetExtension(tree);
            break;

        case DafnyParser.LISTEX:
            result = buildListExtension(tree);
            break;

        case DafnyParser.ALL:
            result = buildQuantifier(Quantifier.FORALL, tree);
            break;

        case DafnyParser.EX:
            result = buildQuantifier(Quantifier.EXISTS, tree);
            break;

        case DafnyParser.LET:
            result = buildLet(tree);
            break;

        case DafnyParser.IF:
            result = buildIf(tree);
            break;

        case DafnyParser.LENGTH:

            // XXX FIXME HACK Sequences length is different
            if(build(tree.getChild(0)).getSort().getName().equals("seq")) {
                System.err.println("Deprecated: Used .Length to access length of sequence: " +
                    tree.toStringTree());
                result = buildCardinality(tree);
            } else {
                result = buildLength(tree);
            }
            break;

        case DafnyParser.CARD:
            result = buildCardinality(tree);
            break;

        case DafnyParser.ARRAY_ACCESS:
            result = buildBracketAccess(tree);
            break;

        case DafnyParser.FIELD_ACCESS:
            result = buildFieldAccess(tree);
            break;

        case DafnyParser.NOETHER_LESS:
            result = buildNoetherLess(tree);
            break;

        case DafnyParser.AT:
            result = buildExplicitHeapAccess(tree);
            break;

        case DafnyParser.HEAP_UPDATE:
            result = buildHeapUpdate(tree);
            break;

        case DafnyParser.CALL:
            result = buildCall(tree);
            break;

        case DafnyParser.WILDCARD:
            result = buildWildcard(tree);
            break;

        case DafnyParser.BLANK:
            result = new SchemaVarTerm("_");
            break;

        case DafnyParser.SCHEMA_ID:
            if(tree.getChildCount() > 0) {
                result = new SchemaCaptureTerm(tree.getText(), build(tree.getChild(0)));
            } else {
                result = new SchemaVarTerm(tree.getText());
            }
            break;

        case DafnyParser.ELLIPSIS:
            result = new SchemaOccurTerm(build(tree.getChild(0)));
            break;

        case DafnyParser.DOUBLE_BLANK:
            // In order to avoid this error message, call "expandMultiBlank" on an arguments
            // DafnyTree (ARGS)
            throw new TermBuildException("__ not supported in this place. "
                    + "Solution: Spell it out using the appropriate number of _. Sorry.");

        case DafnyParser.TYPED_SCHEMA:
            result = build(tree.getChild(0));
            Sort sort = ASTUtil.toSort(tree.getChild(1));
            result = ((SchemaTerm)result).refineSort(sort);
            break;

        default:
            TermBuildException ex =
                new TermBuildException("Cannot translate term: " + tree.toStringTree());
            ex.setLocation(tree);
            throw ex;
        }

        referenceMap.put(result, tree);

        return result;
    }

    private Term buildIf(DafnyTree tree) throws TermBuildException {

        DafnyTree ifTree = tree.getChild(0);
        DafnyTree thenTree = tree.getChild(1);
        DafnyTree elseTree = tree.getChild(2);

        Term ifCond = build(ifTree);
        Term thenExp = build(thenTree);
        Term elseExp = build(elseTree);

        Sort thenSort = thenExp.getSort();
        Sort elseSort = elseExp.getSort();
        Sort sort = Sort.supremum(thenSort, elseSort);

        FunctionSymbol ifFct = BuiltinSymbols.ITE.instantiate(Collections.singletonList(sort));

        return new ApplTerm(ifFct, ifCond, thenExp, elseExp);
    }

    private BiFunctionWithException<Term, Term, FunctionSymbol, TermBuildException>
            symmetricBinarySymbol(FunctionWithException<Sort, FunctionSymbol, TermBuildException> decider) {
        return new BiFunctionWithException<Term, Term, FunctionSymbol, TermBuildException>() {
            @Override
            public FunctionSymbol apply(Term a, Term b) throws TermBuildException {
                Sort sort = Sort.supremum(a.getSort(), b.getSort());
                return decider.apply(sort);
            }
        };
    }

    private Term buildCall(DafnyTree tree) throws TermBuildException {

        assert tree.getChildCount() == 2
                : "Calls with receivers not yet supported!";

        String id = tree.getChild(0).getText();
        FunctionSymbol fct = symbolTable.getFunctionSymbol(id);
        if (fct == null) {
            throw new TermBuildException("Unknown symbol "
                    + id + ". Remember that method calls not allowed in expressions.");
        }

        List<Term> argTerms = new ArrayList<>();
        DafnyTree args = tree.getFirstChildWithType(DafnyParser.ARGS);
        expandMultiBlanks(args, fct.getArity());
        for (DafnyTree arg : args.getChildren()) {
            argTerms.add(build(arg));
        }

        return new ApplTerm(fct, argTerms);
    }


    private Term buildBracketAccess(DafnyTree tree) throws TermBuildException {

        Term arrayTerm = build(tree.getChild(0));
        Sort arraySort = arrayTerm.getSort();
        String arraySortName = arraySort.getName();

        Term indexTerm;

        switch (arraySortName) {
            case "array":
                if (tree.getChildCount() != 2) {
                    throw new TermBuildException("Access to 'array' requires one index argument");
                }

                indexTerm = build(tree.getChild(1));

                return tb.selectArray(getHeap(), arrayTerm, indexTerm);

            case "seq":
                if (tree.getChildCount() != 2) {
                    throw new TermBuildException("Access to 'array' requires one index argument");
                }

                indexTerm = build(tree.getChild(1));

                return tb.seqGet(arrayTerm, indexTerm);

        case "array2":
                if (tree.getChildCount() != 3) {
                    throw new TermBuildException("Access to 'array2' requires two index arguments");
                }

                Term index0 = build(tree.getChild(1));
                Term index1 = build(tree.getChild(2));

                return tb.selectArray2(new ApplTerm(BuiltinSymbols.HEAP),
                        arrayTerm, index0, index1);

        case "heap":
            DafnyTree indexTree = tree.getChild(1);
            if(indexTree.getType() != DafnyParser.CALL) {
                throw new TermBuildException("Heap updates must be applied to function calls");
            }

            List<Term> arguments = new ArrayList<>();
            arguments.add(arrayTerm);
            for (DafnyTree dafnyTree : indexTree.getFirstChildWithType(DafnyParser.ARGS).getChildren()) {
                arguments.add(build(dafnyTree));
            }

            String name = indexTree.getChild(0).getText();
            FunctionSymbol fs = symbolTable.getFunctionSymbol(name);
            if (fs == null) {
                throw new TermBuildException("Unknown symbol heap update function " + name);
            }

            return new ApplTerm(fs, arguments);

            default:
                throw new TermBuildException("Unsupported array sort: " + arraySort);
        }
    }

    private Term buildFieldAccess(DafnyTree tree) throws TermBuildException {

        Term receiver = build(tree.getChild(0));

        if(!receiver.getSort().isClassSort()) {
            throw new TermBuildException("field access only possible for class sorts");
        }

        String classId = receiver.getSort().toString();
        String fieldId = tree.getChild(1).getText();
        String fieldName = TermBuilder.fieldName(classId, fieldId);
        FunctionSymbol field = symbolTable.getFunctionSymbol(fieldName);

        if(field == null) {
            throw new TermBuildException("Field " + fieldId + " not found in class " + classId);
        }

        return tb.selectField(getHeap(), receiver, new ApplTerm(field));
    }


    private Term buildLength(DafnyTree tree) throws TermBuildException {
        String functionName = tree.toString();
        String suffix = functionName.substring(6);

        int index = 0;
        if (suffix.length() > 0) {
            index = Integer.parseInt(suffix);
        }

        Term t1 = build(tree.getChild(0));
        Sort sort = t1.getSort();
        Sort arg;
        FunctionSymbol f;

        switch (sort.getName()) {
            case "array":
                if (!suffix.isEmpty()) {
                    throw new TermBuildException("Elements of type 'array' have only "
                            + "the 'Length' property");
                }
                arg = sort.getArguments().get(0);
                f = symbolTable.getFunctionSymbol("$len<" + arg + ">");
                break;

            case "array2":
                if (!suffix.matches("[01]")) {
                    throw new TermBuildException("Elements of type 'array2' have only "
                            + "the 'Length0' and 'Length1' properties");
                }

                arg = sort.getArguments().get(0);
                f = symbolTable.getFunctionSymbol("$len" + index + "<" + arg + ">");
                break;

            default:
                throw new TermBuildException("Unsupported sort for '" +
                        functionName + "': " + sort);
        }

        return new ApplTerm(f, t1);
    }

    private Term buildCardinality(DafnyTree tree) throws TermBuildException {

        Term inner = build(tree.getChild(0));
        FunctionSymbol function;

        Sort sort = inner.getSort();
        switch (sort.getName()) {
        case "set":
            function = BuiltinSymbols.CARD.instantiate(
                    sort.getArguments().get(0));
            break;

        case "seq":
            function = BuiltinSymbols.SEQ_LEN.instantiate(
                    sort.getArguments().get(0));
            break;

        default:
            throw new TermBuildException("Unsupported sort for |...|: " + sort);
        }

        return new ApplTerm(function, inner);
    }

    private Term buildWildcard(DafnyTree tree) throws TermBuildException {
        Sort sort = buildSort(tree.getExpressionType());
        if (tree.getChildCount() > 0) {
            return build(tree.getChild(0));
        }
        String suggestedName;
        suggestedName = "unknown";

        int count = 1;
        String name = suggestedName + "_" + count;
        while (symbolTable.getFunctionSymbol(name) != null) {
            count++;
            name = suggestedName + "_" + count;
        }

        FunctionSymbol fs = new FunctionSymbol(name, sort);
        symbolTable.addFunctionSymbol(fs);

        return new ApplTerm(fs);
    }


    private Term buildNull(DafnyTree tree) throws TermBuildException {
        return tb._null();
    }

    // can be reused by set, seq and multiset
    private Term buildExtension(FunctionSymbolFamily emptyFamily,
                                FunctionSymbolFamily addFamily,
                                DafnyTree tree) throws TermBuildException {

        assert tree.getChildCount() > 0 :
                "Currently empty list and set are not supported via extensions";

        Sort sort = null;
        List<Term> arguments = new ArrayList<>();

        for (DafnyTree child : tree.getChildren()) {
            Term term = build(child);
            arguments.add(term);
            Sort termSort = term.getSort();
            if (sort == null) {
                sort = termSort;
            } else {
                if (!termSort.equals(sort)) {
                    if (termSort.isClassSort() && sort.isClassSort()) {
                        sort = Sort.OBJECT;
                    } else {
                        throw new TermBuildException(
                                "List extension with incomparable types: " +
                                        sort + " and " + termSort);
                    }
                }
            }
        }

        FunctionSymbol add = addFamily.instantiate(sort);
        FunctionSymbol empty = emptyFamily.instantiate(sort);

        ApplTerm result = new ApplTerm(empty);
        for (Term term : arguments) {
            result = new ApplTerm(add, term, result);
        }

        return result;
    }

    private Term buildListExtension(DafnyTree tree) throws TermBuildException {
        return buildExtension(BuiltinSymbols.SEQ_EMPTY, BuiltinSymbols.SEQ_CONS, tree);
    }

    private Term buildSetExtension(DafnyTree tree) throws TermBuildException {
        return buildExtension(BuiltinSymbols.EMPTY_SET, BuiltinSymbols.SET_ADD, tree);
    }

    private Term buildIdentifier(DafnyTree tree) throws TermBuildException {
        String name = tree.toString();
        VariableTerm var = boundVars.get(name);
        if (var != null) {
            // found a bound variable in context!
            return var;
        }

        DafnyTree decl = tree.getDeclarationReference();
        if (decl != null && decl.getType() == DafnyParser.FIELD) {
            // if there is a field by that name ...
            Term field = tb.makeFieldConst(decl.getParent().getChild(0).getText(), name);
            Term self = tb.self();
            return tb.selectField(getHeap(), self, field);
        }

        FunctionSymbol fct = symbolTable.getFunctionSymbol(name);
        if (fct == null) {
            throw new TermBuildException("Unknown identifier " + name);
        }

        return new ApplTerm(fct);
    }

    private Term buildQuantifier(Quantifier q, DafnyTree tree) throws TermBuildException {
        assert tree.getChildCount() >= 3;

        ImmutableList<DafnyTree> vars =
                ImmutableList.from(
                        tree.getChildren().subList(0, tree.getChildCount() - 2));

        // make the order correct
        vars = vars.reverse();

        Sort sort = buildSort(tree.getFirstChildWithType(DafnyParser.TYPE).getChild(0));

        DafnyTree formulaTree = tree.getLastChild();
        return buildQuantifier(q, vars, sort, formulaTree);
    }


    private Term buildQuantifier(Quantifier q, ImmutableList<DafnyTree> vars, Sort sort, DafnyTree formulaTree) throws TermBuildException {
        if(vars.size() == 0) {
            return build(formulaTree);
        }

        DafnyTree var = vars.getHead();
        VariableTerm varTerm = new VariableTerm(var.getText(), sort);
        boundVars.put(varTerm.getName(), varTerm);
        try {
            Term inner = buildQuantifier(q, vars.getTail(), sort, formulaTree);
            Term result = new QuantTerm(q, varTerm, inner);
            return result;
        } finally {
            boundVars.pop();
        }

    }

    private Term buildLet(DafnyTree tree) throws TermBuildException {

        List<DafnyTree> targets = tree.getChild(0).getChildren();

        if (targets.size() + 2 != tree.getChildCount()) {
            throw new TermBuildException("Mismatched assignments in let expression: "
                    + targets.size() + " variables, but "
                    + (tree.getChildCount() - 2) + " expressions.");
        }

        List<Pair<VariableTerm, Term>> substs = new ArrayList<>();
        for (int i = 0; i < targets.size(); i++) {
            Term term = build(tree.getChild(i+1));
            VariableTerm var = new VariableTerm(targets.get(i).getText(), term.getSort());
            substs.add(new Pair<>(var, term));
        }

        // only bind them now after all expressions have been parsed
        int rewindPos = boundVars.getHistory();
        try {
            for (Pair<VariableTerm, Term> pair : substs) {
                boundVars.put(pair.fst.getName(), pair.fst);
            }

            Term inner = build(tree.getLastChild());
            LetTerm result = new LetTerm(substs, inner);
            return result;
        } finally {
            boundVars.rewindHistory(rewindPos);
        }

    }


    // Currently that is still simple since only array<int>, arrayN<int> and set<int>
    // are supported besides int.
    // The name of the node is actually the type already... Will change in future!
    private Sort buildSort(@NonNull DafnyTree child) {
        return SymbexStateToFormula.treeToType(child);
    }

    private Term buildUnary(FunctionSymbol f, DafnyTree tree) throws TermBuildException {
        if (tree.getChildCount() != 1) {
            throw new RuntimeException("Unexpected argument " + tree.toStringTree());
        }

        Term t1 = build(tree.getChild(0));
        return new ApplTerm(f, Collections.singletonList(t1));
    }

    private Term buildBinary(FunctionSymbol f, DafnyTree tree) throws TermBuildException {
        assert tree.getChildCount() == 2 :
            "Unexpected argument " + tree.toStringTree();

        Term t1 = build(tree.getChild(0));
        Term t2 = build(tree.getChild(1));
        return new ApplTerm(f, Arrays.asList(t1, t2));
    }
    
    private Term buildBinary(
            BiFunctionWithException<Term, Term, FunctionSymbol, TermBuildException> functionDecider,
            DafnyTree tree) throws TermBuildException {
        assert tree.getChildCount() == 2 :
                "Unexpected argument " + tree.toStringTree();

        Term t1 = build(tree.getChild(0));
        Term t2 = build(tree.getChild(1));
        FunctionSymbol f = functionDecider.apply(t1, t2);
        return new ApplTerm(f, Arrays.asList(t1, t2));
    }

    private Term buildNoetherLess(DafnyTree tree) throws TermBuildException {
        // TODO refactor this for seq<?> one day when seqs are available

        DafnyTree lhs = tree.getChild(0);
        DafnyTree rhs = tree.getChild(1);

        assert lhs.getType() == DafnyParser.LISTEX
                && rhs.getType() == DafnyParser.LISTEX
                && lhs.getChildCount() == rhs.getChildCount() :
                "limited support so far, we inline the comparison";

        Term result = tb.ff();
        Term[] vars = new Term[rhs.getChildCount()];
        Term[] terms = new Term[rhs.getChildCount()];

        for (int i = 0; i < rhs.getChildCount(); i++) {
            vars[i] = build(lhs.getChild(i));
            terms[i] = build(rhs.getChild(i));

            Term cond = tb.tt();
            for (int j = 0; j < i; j++) {
                ApplTerm eq = tb.eq(terms[j], vars[j]);
                cond = tb.and(cond, eq);
            }

            cond = tb.and(cond, tb.lessEqual(tb.zero, terms[i]));
            cond = tb.and(cond, tb.less(terms[i], vars[i]));
            result = tb.or(result, cond);
        }

        return result;
    }

    private Term buildExplicitHeapAccess(DafnyTree tree) throws TermBuildException {

        Term heapAccess = build(tree.getChild(0));
        Term heapTerm = build(tree.getChild(1));

        if(!(heapAccess instanceof ApplTerm)) {
            throw new TermBuildException("heap suffixes are only allowed for heap select terms");
        }

        ApplTerm appl = (ApplTerm) heapAccess;
        if(appl.countTerms() < 1 || !appl.getTerm(0).getSort().equals(Sort.HEAP)) {
            throw new TermBuildException("heap suffixes are only allowed for heap select terms");
        }

        if(!heapTerm.getSort().equals(Sort.HEAP)) {
            throw new TermBuildException("heap suffixes must specify a heap");
        }

        ArrayList<Term> args = new ArrayList<>(heapAccess.getSubterms());
        args.set(0, heapTerm);

        return new ApplTerm(appl.getFunctionSymbol(), args);
    }

    private Term buildHeapUpdate(DafnyTree tree) throws TermBuildException {

        assert tree.getChildCount() == 3 : "I need heap, location, value";

        Term heap = build(tree.getChild(0));
        if(!heap.getSort().equals(Sort.HEAP)) {
            throw new TermBuildException("Heap updates must be applied to heaps");
        }

        FunctionSymbolFamily symbol;
        Term location = build(tree.getChild(1));
        try {
            ApplTerm appl = (ApplTerm) location;
            FunctionSymbol fs = appl.getFunctionSymbol();
            InstantiatedFunctionSymbol ifs = (InstantiatedFunctionSymbol) fs;
            symbol = ifs.getFamily();
        } catch(ClassCastException ex) {
            throw new TermBuildException("Heap updates must modify a heap location", ex);
        }

        Term value = build(tree.getChild(2));

        if(symbol == BuiltinSymbols.SELECT) {
            Term obj = location.getTerm(1);
            Term field = location.getTerm(2);
            FunctionSymbol store = BuiltinSymbols.STORE.instantiate(obj.getSort(), location.getSort());
            return new ApplTerm(store, heap, obj, field, value);

        } else if(symbol == BuiltinSymbols.ARRAY_SELECT) {
            Term obj = location.getTerm(1);
            Term index = location.getTerm(2);
            // TODO make this right. ...
            FunctionSymbol store = BuiltinSymbols.ARRAY_STORE.instantiate(obj.getSort().getArguments().get(0));
            return new ApplTerm(store, heap, obj, index, value);

        } else if(symbol == BuiltinSymbols.ARRAY2_SELECT) {
            throw new Error("Not implemented, yet");

        } else {
            throw new TermBuildException("Heap updated must modify a heap location");
        }
    }

    /*
     * Take a ARGS tree and expand the __ that it might contain into several _.
     *
     * By the grammar, __ can only be the first or last element of an expression
     * list.
     *
     * The value targetArity specifies the number of elements that args should
     * have in the end.
     */
    private void expandMultiBlanks(DafnyTree args, int targetArity) {
        DafnyTree first = args.getChild(0);
        DafnyTree last = args.getLastChild();
        int childCount = args.getChildCount();

        if (first.getType() == DafnyParser.DOUBLE_BLANK) {
            CommonToken token = new CommonToken(first.getToken());
            token.setType(DafnyParser.BLANK);
            args.replaceChildren(0, 0, new DafnyTree(token));

            for (int i = childCount; i < targetArity; i++) {
                token = new CommonToken(first.getToken());
                token.setType(DafnyParser.BLANK);
                args.insertChild(0, new DafnyTree(token));
            }
        } else

        if (last.getType() == DafnyParser.DOUBLE_BLANK) {
            CommonToken token = new CommonToken(first.getToken());
            token.setType(DafnyParser.BLANK);
            args.replaceChildren(childCount-1, childCount-1, new DafnyTree(token));

            for (int i = childCount; i < targetArity; i++) {
                token = new CommonToken(first.getToken());
                token.setType(DafnyParser.BLANK);
                args.addChild(new DafnyTree(token));
            }
        }

        assert args.getChildren().stream()
                .allMatch(x -> x.getType() != DafnyParser.DOUBLE_BLANK);
    }


    /* for testing */
    int countBoundVars() {
        return boundVars.size();
    }


    /**
     * Retrieves a map which assigns to every term the {@link DafnyTree} origin.
     *
     * Caution! This map is an identity map which maps to every term OBJECT
     * IDENTITY. Two terms which are semantically and structurally equal may
     * have different origins!
     *
     * @return the reference map
     */
    public Map<Term, DafnyTree> getReferenceMap() {
        return referenceMap;
    }

    // TODO doc when TAT is finished
    public void bindVariable(VariableTerm var) {
        boundVars.put(var.getName(), var);
    }

    public void unbindVariable(VariableTerm var) {
        if (!boundVars.peek().equals(var)) {
            throw new IllegalStateException("This is not the last bound variable");
        }
        boundVars.pop();
    }
}