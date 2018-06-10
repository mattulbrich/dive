package edu.kit.iti.algover.smttrans.translate.expressions;

public class SMTVarExpression extends SMTExpression {

    private String name;
    private SMTExpression partner;

    public SMTVarExpression(String name, SMTExpression partner) {
        super();
        this.name = name;
        this.partner = partner;
    }

    @Override
    public String toSMT() {
        StringBuilder sb = new StringBuilder();
//        LinkedHashSet<Dependency> set = new LinkedHashSet<>();
//        set.add(new ConstDependency(this.name, new Type(Type.typeConst(this.name).getName())));
        sb.append("(");
        sb.append("="); //TODO eq
        sb.append(" ");
        sb.append(this.name);
        sb.append(" ");
        sb.append(partner.toSMT());
       sb.append(") ");
//        
//        return new Pair<LinkedHashSet<Dependency>, String>(set,sb.toString());
        return sb.toString();
    }

}
