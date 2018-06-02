package edu.kit.iti.algover.smttrans.translate.expressions;

import java.util.Collection;
import java.util.List;

import edu.kit.iti.algover.smttrans.data.Operation;
import edu.kit.iti.algover.smttrans.data.OperationMatcher;
import edu.kit.iti.algover.smttrans.translate.Type;

public abstract class SMTExpression {

	protected Operation op;
	protected Type type;
	protected List<SMTExpression> children;

	public abstract String toPSMT();
	
	public SMTExpression(String op, Type type, List<SMTExpression> children) {
		this.op = OperationMatcher.matchOp(op);
		this.type = type;
		this.children = children;
	}
	
	

}
