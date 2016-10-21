package edu.kit.iti.algover.dafnystructures;

import edu.kit.iti.algover.parser.DafnyTree;

import java.io.File;
import java.util.List;

/**
 * Created by sarah on 8/4/16.
 */
public class DafnyMethod extends DafnyDecl {

    private String methodName;
    private List<DafnyTree> params;
    private List<DafnyTree> returns;

    public String getMethodName() {
        return methodName;
    }

    public List<DafnyTree> getParams() {
        return params;
    }

    public List<DafnyTree> getReturns() {
        return returns;
    }

    public DafnyTree getBody() {
        return body;
    }

    public List<DafnyTree> getPres() {
        return pres;
    }

    public List<DafnyTree> getPosts() {
        return posts;
    }

    /**
     * The function's body. Only one single line allowed
     */
    private DafnyTree body;


    private List<DafnyTree> pres;
    private List<DafnyTree> posts;

    public DafnyMethod(File file, DafnyTree t, String methodName, List<DafnyTree> params,
                       List<DafnyTree> returns,
                       DafnyTree body,
                       List<DafnyTree> pres,
                       List<DafnyTree> posts) {
        super(file, t, methodName);
        this.methodName = methodName;
        this.params = params;
        this.returns = returns;
        this.body = body;
        this.pres = pres;
        this.posts = posts;
    }

    public String toString() {
        String s = "method " + this.methodName + "\n";

        if (this.params != null) {
            String params = this.params.size() + " Parameters: ";

            for (DafnyTree para : this.params) {
                params += para.toStringTree() + "\n";
            }
            s += params + "\n";
        }
        return s;

    }
    @Override
    public <R, A> R accept(DafnyDeclVisitor<R,A> visitor, A arg) {
        return visitor.visit(this, arg);
    }

}
