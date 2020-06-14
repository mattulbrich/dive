/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.boogie;

import de.uka.ilkd.pp.NoExceptions;
import edu.kit.iti.algover.dafnystructures.DafnyClass;
import edu.kit.iti.algover.dafnystructures.DafnyFunction;
import edu.kit.iti.algover.dafnystructures.DafnyFunctionSymbol;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.DefaultTermVisitor;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.FunctionSymbolFamily.InstantiatedFunctionSymbol;
import edu.kit.iti.algover.term.LetTerm;
import edu.kit.iti.algover.term.QuantTerm;
import edu.kit.iti.algover.term.QuantTerm.Quantifier;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.VariableTerm;
import edu.kit.iti.algover.util.Util;
import nonnull.NonNull;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.Function;

import static edu.kit.iti.algover.data.BuiltinSymbols.*;
import static edu.kit.iti.algover.data.BuiltinSymbols.MULTI_SET_IN;

/**
 * This visitor is used to translate AlgoVer {@link Term} objects into Strings
 * representing corresponding (semantically equivalent in their respective
 * logics) Strings in Boogie.
 *
 * The translation is restricted to a part of the logic.
 *
 * A table is kept for the built in function symbols which are translated using
 * the functions stored in that map. The interface {@link Boogiefier} is used for
 * such translation functions.
 *
 * (I have been using Scala lately. One can tell.)
 *
 * @author mulbrich
 */
public class BoogieVisitor extends DefaultTermVisitor<Void, String, NoExceptions> {

    private static final Function<Term, Term> EMPTY_TRIGGER = t -> null;

    /**
     * The functional interface for the routines which translate individual
     * function symbols.
     */
    @FunctionalInterface
    private interface Boogiefier {

        /**
         * Translate a term into a Boogie string
         * @param term the term to translate, not null
         * @param visitor the visitor to use for subterms, not null
         * @return a non-null String
         */
        String translate(ApplTerm term, BoogieVisitor visitor);

    }
    private static final Map<String, Boogiefier> FUNCTIONS = prepareMap();

    private static Map<String, Boogiefier> prepareMap() {
        Map<String, Boogiefier> result = new HashMap<>();
        // --- Integers
        result.put(PLUS.getName(), binary("+"));
        result.put(MINUS.getName(), binary("-"));
        result.put(TIMES.getName(), binary("*"));
        result.put(DIV.getName(), binary(" div "));
        result.put(GE.getName(), binary(">="));
        result.put(GT.getName(), binary(">"));
        result.put(LE.getName(), binary("<="));
        result.put(LT.getName(), binary("<"));
        result.put(NEG.getName(), (t,v) -> "-(" + t.getTerm(0).accept(v, null) + ")");
        // --- FOL
        result.put(EQ.getBaseName(), equal());
        result.put(TRUE.getName(), constant("true"));
        result.put(FALSE.getName(), constant("false"));
        result.put(AND.getName(), binary("&&"));
        result.put(IMP.getName(), binary("==>"));
        result.put(OR.getName(), binary("||"));
        result.put(NOT.getName(), (t,v) -> "!("+t.getTerm(0).accept(v,null)+")");
        result.put(ITE.getBaseName(), format("(if %s then %s else %s)"));
        // --- Sets
        result.put(SUBSET.getBaseName(), function("Set#Subset"));
        result.put(UNION.getBaseName(), function("Set#Union"));
        result.put(INTERSECT.getBaseName(), function("Set#Intersection"));
        result.put(SET_MINUS.getBaseName(), function("Set#Difference"));
        result.put(UNION.getBaseName(), function("Set#Union"));
        result.put(SET_ADD.getBaseName(), function("Set#UnionOne", true));
        result.put(SET_IN.getBaseName(), setIn());
        result.put(EMPTY_SET.getName(), function("Set#Empty"));
        result.put(CARD.getBaseName(), function("Set#Card"));
        // --- Multisets
        result.put(MULTI_SUBSET.getBaseName(), function("MultiSet#Subset"));
        result.put(MULTI_UNION.getBaseName(), function("MultiSet#Union"));
        result.put(MULTI_INTERSECT.getBaseName(), function("MultiSet#Intersection"));
        result.put(MULTI_SET_MINUS.getBaseName(), function("MultiSet#Difference"));
        result.put(MULTI_UNION.getBaseName(), function("MultiSet#Union"));
        result.put(MULTI_SET_ADD.getBaseName(), function("MultiSet#UnionOne", true));
        result.put(MULTI_SET_IN.getBaseName(), multisetIn());
        result.put(EMPTY_MULTI_SET.getName(), function("MultiSet#Empty"));
        result.put(MULTI_CARD.getBaseName(), function("MultiSet#Card"));
        result.put(MULTI_SET_ELEM_CARD.getBaseName(), multisetElemCard());
        result.put("multiset", toMultiset());
        // --- Sequents
        result.put(SEQ_LEN.getBaseName(), function("Seq#Length"));
        result.put(SEQ_GET.getBaseName(), function("Seq#Index"));
        result.put(SEQ_EMPTY.getName(), function("Seq#Empty"));
        result.put(SEQ_UPDATE.getBaseName(), function("Seq#Update"));
        result.put(SEQ_SUB.getBaseName(), seqSub());
        result.put(SEQ_CONS.getBaseName(), function("Seq#Build", true));
        result.put(SEQ_CONCAT.getBaseName(), function("Seq#Append"));
        // --- Heaps
        result.put(ARRAY_SELECT.getBaseName(), arraySelect(1));
        result.put(ARRAY_STORE.getBaseName(), arrayStore(1));
        result.put(STORE.getBaseName(), function("update"));
        result.put(ANON.getName(), function("anon"));
        result.put(SELECT.getBaseName(), function("read"));
        result.put(LEN.getBaseName(), function("_System.array.Length"));
        result.put(NULL.getName(), constant("null"));
        result.put(IS_CREATED.getName(), function("$IsCreated"));
        result.put(FRESH_OBJECTS.getName(), function("$FreshObjects"));
        result.put(ARRAY_TO_SEQ.getBaseName(), array2seq());
        return result;
    }

    private static Boogiefier arrayStore(int dimension) {
        return (t,v) ->
                String.format("update(%s, %s, IndexField(%s) : Field %s, %s)",
                t.getTerm(0).accept(v, null),
                t.getTerm(1).accept(v, null),
                t.getTerm(2).accept(v, null),
                visitSort(t.getTerm(3).getSort()),
                t.getTerm(3).accept(v, null));
    }

    // update($Heap, a#0, IndexField(LitInt(0)), $Box($rhs#0));
    private static Boogiefier format(String format) {
        return (t,v) -> {
            String[] args = new String[t.countTerms()];
            for (int i = 0; i < args.length; i++) {
                args[i] = t.getTerm(i).accept(v, null);
            }
            return String.format(format, (Object[])args);
        };
    }

    private static Boogiefier arraySelect(int dimension) {

        return (t,v) ->
            String.format("read(%s, %s, IndexField(%s) : Field %s)",
                    t.getTerm(0).accept(v, null),
                    t.getTerm(1).accept(v, null),
                    t.getTerm(2).accept(v, null),
                    visitSort(t.getSort())
                    );

    }

    private static Boogiefier seqSub() {
        return (t,v) -> {
            String seq = t.getTerm(0).accept(v, null);
            String from = t.getTerm(1).accept(v, null);
            String to = t.getTerm(2).accept(v, null);
            return "Seq#Drop(Seq#Take(" + seq + ", " + to + "), " + from + ")";
        };
    }
    private static Boogiefier array2seq() {
        return (t,v) -> {
            String heap = t.getTerm(0).accept(v, null);
            Term array = t.getTerm(1);
            String arg = array.accept(v, null);
            return "(Seq#FromArray(" + heap + ", " + arg +
                    "): Seq " + visitSort(array.getSort().getArgument(0)) + ")";
        };
    }


    private static Boogiefier toMultiset() {
        return (t,v) -> {
            Term arg = t.getTerm(0);
            String argTrans = arg.accept(v, null);
            switch(arg.getSort().getName()) {
            case "set": return "MultiSet#FromSet(" + argTrans + ")";
            case "seq": return "MultiSet#FromSeq(" + argTrans + ")";
            default: throw new Error("not covered by the implementation: " + t.getSort());
            }
        };
    }


    /*
     * Returns a Boogiefier that translates
     *    f(x, ..., y)
     * into
     *    fctName(v(x), ..., v(y)
     * where v(...) is the applcation of the provided visitor.
     */
    private static final Boogiefier function(String fctName) {
        return function(fctName, false);
    }

    /*
     * Returns a constant string regardless of the parameter
     */
    private static final Boogiefier constant(String string) {
        return (t,v) -> string;
    }

    /*
     * Returns a Boogiefier that translates
     *    f(x, ..., y)
     * into
     *    fctName(v(x), ..., v(y))
     * if reverse == false and
     *    fctName(v(y), ..., v(x))
     * otherwie
     * where v(...) is the application of the provided visitor.
     */
    private static Boogiefier function(String fctName, boolean reverse) {

        return (t,v) -> {
            StringBuilder sb = new StringBuilder(fctName);
            List<String> visited = Util.map(t.getSubterms(), x -> x.accept(v, null));
            if (reverse) {
                Collections.reverse(visited);
            }
            sb.append("(").append(Util.commatize(visited)).append(")");
            return sb.toString();
        };
    }

    /*
     * Equal is special. x==y becomes:
     *    Set#Equal(v(x), v(y)) for sets
     *    MultiSet#Equal(v(x), v(y)) for multisets
     *    Seq#Equal(v(x), v(y)) for sequences
     *    (v(x)==v(y))  otherwise
     */
    private static final Boogiefier equal() {
        return (t, v) -> {
            Boogiefier f;
            switch (t.getTerm(0).getSort().getName()) {
            case "set":
                f = function("Set#Equal");
                break;
            case "multiset":
                f = function("MultiSet#Equal");
                break;
            case "seq":
                f = function("Seq#Equal");
                break;
            default:
                f = binary("==");
                break;
            }
            return f.translate(t, v);
        };
    }

    /*
     * For set membership, Boogie uses map syntax:
     *    set_in(e, s)    becomes    ( v(s) [ v(e) ])
     */
    private static Boogiefier setIn() {
        return (t,v) -> {
            String set = t.getTerm(1).accept(v, null);
            String elem = t.getTerm(0).accept(v, null);
            return "(" + set + "[" + elem + "])";
        };
    }

    /*
     * For multiset membership, Boogie uses map syntax:
     *    multi_set_in(e, s)    becomes    ( v(s) [ v(e) ] > 0)
     */
    private static Boogiefier multisetIn() {
        return (t,v) -> {
            String set = t.getTerm(1).accept(v, null);
            String elem = t.getTerm(0).accept(v, null);
            return "(" + set + "[" + elem + "] > 0)";
        };
    }

    private static Boogiefier multisetElemCard() {
        return (t, v) -> {
            String ms = t.getTerm(1).accept(v, null);
            String elem = t.getTerm(0).accept(v, null);
            return ms + "[" + elem + "]";
        };
    }


    /*
     *  Binary infix symbol. f(x,y) becomes
     *     "(" v(x) "op" v(y) ")"
     */
    private static Boogiefier binary(String op) {
        return (t,v) -> {
            assert t.countTerms()==2;
            String left = t.getTerm(0).accept(v, null);
            String right = t.getTerm(1).accept(v, null);
            return "(" + left + " " + op + " " + right + ")";
        };
    }


    // ------------------ End of static part
    /**
     * This collection keeps all required declarations which were collected
     * so far.
     */
    private Set<String> declarations = new TreeSet<>();

    private List<String> axioms = new ArrayList<>();

    private @NonNull Function<Term, Term> triggerFunction = EMPTY_TRIGGER;

    /*
     * Check for an entry in the map, otherwise declare the constant.
     */
    @Override
    public String visit(ApplTerm term, Void arg) {
        FunctionSymbol fs = term.getFunctionSymbol();
        String name = fs.getName();
        if (fs instanceof InstantiatedFunctionSymbol) {
            InstantiatedFunctionSymbol instantiatedFunctionSymbol = (InstantiatedFunctionSymbol) fs;
            name = instantiatedFunctionSymbol.getFamily().getBaseName();
        }

        if (name.matches("[0-9]+")) {
            // Numbers are function symbols, too.
            return name;
        }

        Boogiefier handler = FUNCTIONS.get(name);
        if (handler != null) {
            return handler.translate(term, this);
        }

        if (fs instanceof InstantiatedFunctionSymbol) {
            throw new RuntimeException("This should have been in the table: " + name);
        }

        String fctName = addDeclarations(fs);

        if (fs.getArity() == 0) {
            return fctName;
        } else {
            return function(fctName).translate(term, this);
        }
    }

    private String addDeclarations(FunctionSymbol fs) {

        String name, args, type;
        if(fs.getArity() == 0) {
            type = "const";
            name = "_" + fs.getName();
            args = "";
            if(fs.getName().contains("$$") && fs.getResultSort().getName().equals("field")) {
                // Field constants are special!
                type = "const unique";
            }
        } else {
            type = "function";
            name = "f_" + fs.getName();
            args = "(" + Util.commatize(Util.map(fs.getArgumentSorts(), BoogieVisitor::visitSort)) + ")";
        }

        boolean added = declarations.add(
                String.format("%s %s%s : %s;",
                        type, name, args,
                        visitSort(fs.getResultSort())));

        // is indeed a new symbol
        if (added) {
            if(fs.getArity() == 0) {
                axioms.add(String.format("axiom $Is(%s, %s);",
                        name, typeConstant(fs.getResultSort())));
            } else {
                StringBuilder quants = new StringBuilder();
                List<String> arglist = new ArrayList<>();
                int i = 0;
                for (Sort argSort : fs.getArgumentSorts()) {
                    quants.append("(forall v" + i + ": " + visitSort(argSort) + " :: ");
                    arglist.add("v" + i);
                    i++;
                }
                axioms.add(String.format("axiom %s $Is(%s(%s), %s) %s;",
                        quants, name, Util.commatize(arglist),
                        typeConstant(fs.getResultSort()),
                        Util.duplicate(")", i)));
            }
        }

        return name;
    }
    @Override
    protected String defaultVisit(Term term, Void arg) throws NoExceptions {
        throw new IllegalStateException("This should not be reached");
    }

    @Override
    public String visit(LetTerm term, Void arg) throws NoExceptions {
        throw new IllegalStateException("This should not be reached. " +
                "Let-expressions should have been resolved");
    }


    /*
     * Variables are prefixed with var_
     */

    @Override
    public String visit(VariableTerm term, Void arg) throws NoExceptions {
        return "var_" + term.getName();
    }
    /*
     * Quantifiers are straight forward.
     */

    @Override
    public String visit(QuantTerm quantTerm, Void arg) throws NoExceptions {
        String quantifier = quantTerm.getQuantifier() == Quantifier.FORALL ?
                "forall" : "exists";

        StringBuilder sb = new StringBuilder("(" + quantifier);
        Term term = quantTerm;
        while (term instanceof QuantTerm) {
            QuantTerm innerQuant = (QuantTerm) term;
            if (innerQuant.getQuantifier() != quantTerm.getQuantifier()) {
                break;
            }
            if (term != quantTerm) {
                sb.append(",");
            }
            sb.append(" var_" + innerQuant.getBoundVar().getName() + ":" +
                    visitSort(innerQuant.getBoundVar().getSort()));
            term = term.getTerm(0);
        }

        sb.append(" :: ");
        Term trigger = triggerFunction.apply(term);
        if (trigger != null) {
            sb.append("{").append(trigger.accept(this, null)).append("} ");
        }

        sb.append(term.accept(this, null)).append(")");
        return sb.toString();
    }

    public void addClassDeclarations(Project project) {

        for (DafnyClass dafnyClass : project.getClasses()) {
            String name = dafnyClass.getName();
            declarations.add(String.format("const unique TClass_%s : Ty;",
                    name));
            axioms.add(String.format("axiom (forall x:ref :: $Is(x, TClass_%s) <==> " +
                            "dtype(x) == TClass_%s || x == null);",
                    name, name));
        }
    }

    private static String visitSort(Sort sort) {
        switch(sort.getName()) {
        case "seq" :
            return "Seq (" + visitSort(sort.getArgument(0)) + ")";
        case "set" :
            return "Set (" + visitSort(sort.getArgument(0)) + ")";
        case "multiset" :
            return "MultiSet (" + visitSort(sort.getArgument(0)) + ")";
        case "bool":
        case "int":
            return sort.getName();
        case "field":
            return "Field (" + visitSort(sort.getArgument(1)) + ")";
        case "heap":
            return "Heap";
        default:
            return "ref";
        }
    }
    private static String typeConstant(Sort sort) {
        switch(sort.getName()) {
        case "seq" :
            return "TSeq(" + typeConstant(sort.getArgument(0)) + ")";
        case "set" :
            return "TSet(" + typeConstant(sort.getArgument(0)) + ")";
        case "multiset" :
            return "TMultiSet(" + typeConstant(sort.getArgument(0)) + ")";
        case "bool":
            return "TBool";
        case "int":
            return "TInt";
        case "field":
            return "TField(" + typeConstant(sort.getArgument(1)) + ")";
        case "heap":
            return "THeap";
        case "array":
            return "TArray(" + typeConstant(sort.getArgument(0)) + ")";
        case "object":
            return "TObject";
        default:
            return "TClass_" + sort.getName();
        }
    }

    public Set<String> getDeclarations() {
        return declarations;
    }

    // may even be added to outside!
    public List<String> getAxioms() {
        return axioms;
    }

    public Function<Term, Term> getTriggerFunction() {
        return triggerFunction;
    }

    public void setTriggerFunction(Function<Term, Term> triggerFunction) {
        if(triggerFunction == null) {
            this.triggerFunction = EMPTY_TRIGGER;
        } else {
            this.triggerFunction = triggerFunction;
        }
    }
}
