/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
/**
 * This package contains the nodes of the AST and related classes.
 * <p>
 * <p>
 * <b>How to extend the AST?</b>
 * Inherit from {@link edu.kit.formal.proofscriptparser.ast.ASTNode} with a proper template argument of the corresponding {@link org.antlr.v4.runtime.ParserRuleContext}.
 * You will need to define the {@link edu.kit.formal.proofscriptparser.ast.ASTNode#clone()}
 * and {@link edu.kit.formal.proofscriptparser.ast.ASTNode#accept(edu.kit.formal.proofscriptparser.Visitor)} method.
 *
 * @author Alexander Weigl
 * @version 1 (01.05.17)
 */
package edu.kit.iti.algover.script.ast;

/*-
 * #%L
 * ScriptParser
 * %%
 * Copyright (C) 2017 Application-oriented Formal Verification
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */
