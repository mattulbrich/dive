/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.prettyprint;

import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;

public interface PrettyPrintExtension {

    public boolean canPrint(FunctionSymbol functionSymbol);

    public int getLeftPrecedence(ApplTerm application);

    public int getRightPrecedence(ApplTerm application);

    public void print(ApplTerm application, PrettyPrintVisitor prettyPrintVisitor);

}
