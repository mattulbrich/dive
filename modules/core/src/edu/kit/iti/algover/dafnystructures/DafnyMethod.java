package edu.kit.iti.algover.dafnystructures;

import edu.kit.iti.algover.parser.DafnyTree;

import java.util.List;

/**
 * Created by sarah on 8/4/16.
 */
public class DafnyMethod extends DafnyDecl {

    private String methodName;
    private List<DafnyTree> params;
    private List<DafnyTree> returns;


    /**
     * The function's body. Only one single line allowed
     */
    private DafnyTree body;


    private List<DafnyTree> pres;
    private List<DafnyTree> posts;

    public DafnyMethod(String filename, DafnyTree t, String methodName, List<DafnyTree> params,
                       List<DafnyTree> returns,
                       DafnyTree body,
                       List<DafnyTree> pres,
                       List<DafnyTree> posts) {
        super(filename, t, methodName);
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

}
