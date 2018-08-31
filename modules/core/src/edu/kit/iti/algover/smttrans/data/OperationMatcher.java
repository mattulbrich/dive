package edu.kit.iti.algover.smttrans.data;

import java.util.Arrays;

import java.util.HashMap;
import java.util.List;

import com.google.common.base.Splitter;
import com.google.common.collect.Iterables;

import edu.kit.iti.algover.smttrans.translate.SymbolHandler;

public class OperationMatcher {

    private static HashMap<String, Operation> opmap = new HashMap<>();
    static {
        opmap.put("$let", Operation.LET);
        opmap.put("$const", Operation.CONST);
        opmap.put("$var", Operation.VAR);
        opmap.put("$not", Operation.NOT);
        opmap.put("$ge", Operation.GE);
        opmap.put("$eq", Operation.EQ);
        opmap.put("$array_select", Operation.ARRSELECT);
        opmap.put("$le", Operation.LE);
        opmap.put("$plus", Operation.PLUS);
        opmap.put("$minus", Operation.MINUS);
        opmap.put("$neg", Operation.NEG);
        opmap.put("$times", Operation.TIMES);
        opmap.put("$ite", Operation.ITE);
        opmap.put("$or", Operation.OR);
        opmap.put("$imp", Operation.IMP);
        opmap.put("$and", Operation.AND);
        opmap.put("$lt", Operation.LT);
        opmap.put("$gt", Operation.GT);
        opmap.put("$div", Operation.DIV);
        opmap.put("$array2_select", Operation.ARR2SELECT);
        opmap.put("$len", Operation.ARRLEN);
        opmap.put("$len0", Operation.ARR2LEN0);
        opmap.put("$len1", Operation.ARR2LEN1);
        opmap.put("$store", Operation.FIELDSTORE);
        opmap.put("$array_store", Operation.ARRSTORE);
        opmap.put("$array2_store", Operation.ARR2STORE);
        opmap.put("$select", Operation.FIELDSELECT);

        opmap.put("$decr", Operation.DECR);
        opmap.put("$union", Operation.SETUNION);
        opmap.put("$intersect", Operation.SETINTERSECT);
        opmap.put("$set_minus", Operation.SETMINUS);
        opmap.put("$set_subset", Operation.SETSUBSET);
        opmap.put("$set_single", Operation.SETSINGLE);
        opmap.put("$set_add", Operation.SETADD);
        opmap.put("$set_in", Operation.SETIN);
        opmap.put("$seq_len", Operation.SEQLEN);
        opmap.put("$seq_get", Operation.SEQGET);
        opmap.put("$seq_upd", Operation.SEQUPD);
        opmap.put("$seq_empty", Operation.SEQEMPTY);
        opmap.put("$seq_cons", Operation.SEQCONS);
        opmap.put("$seq_concat", Operation.SEQCONCAT);
        opmap.put("$seq_subselect", Operation.SEQSUBSELECT);
        opmap.put("$seq_single", Operation.SEQSINGLE);
        opmap.put("$anon", Operation.ANON);
        opmap.put("$create", Operation.CREATE);
        opmap.put("$isCreated", Operation.ISCREATED);
        opmap.put("$mod", Operation.MOD);
        opmap.put("$everything", Operation.EVERYTHING);
        opmap.put("$empty", Operation.SETEMPTY);
        opmap.put("$heap", Operation.HEAP);
        opmap.put("$aheap", Operation.AHEAP);

        opmap.put("$multi_minus", Operation.MULTIMINUS);
        opmap.put("$multi_union", Operation.MULTIUNION);
        opmap.put("$multi_intersect", Operation.MULTIINTERSECT);
        opmap.put("$multi_empty", Operation.MULTIEMPTY);

        opmap.put("$multi_set_in", Operation.MULTIIN);
        opmap.put("$multi_set_add", Operation.MULTIADD);
        opmap.put("$multi_set_subset", Operation.MULTISUBSET);

    }

    public static Operation matchOp(String op) {

        Iterable<String> operators = Splitter.on(".").split(op);

        List<String> ops = Arrays.asList(Iterables.toArray(operators, String.class));

        if (opmap.containsKey(ops.get(0))) {
            return opmap.get(ops.get(0));
        } else {
            SymbolHandler.handleFunc(op);
            return Operation.FUNC;
        }

    }
}