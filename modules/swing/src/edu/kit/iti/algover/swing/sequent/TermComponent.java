//    /*
//     * This file is part of AlgoVer.
//     *
//     * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
//     *
//     */
//
//    package edu.kit.iti.algover.swing.sequent;
//
//    import java.awt.Color;
//    import java.awt.Font;
//    import java.awt.Point;
//    import java.awt.datatransfer.Transferable;
//    import java.awt.event.ComponentAdapter;
//    import java.awt.event.ComponentEvent;
//    import java.awt.event.MouseAdapter;
//    import java.awt.event.MouseEvent;
//    import java.awt.event.MouseMotionAdapter;
//    import java.beans.PropertyChangeEvent;
//    import java.beans.PropertyChangeListener;
//    import java.io.IOException;
//    import java.util.ArrayList;
//    import java.util.HashMap;
//    import java.util.List;
//    import java.util.Map;
//    import java.util.Set;
//
//    import javax.swing.BorderFactory;
//    import javax.swing.JPopupMenu;
//    import javax.swing.JTextPane;
//    import javax.swing.SwingUtilities;
//    import javax.swing.TransferHandler;
//    import javax.swing.border.Border;
//    import javax.swing.text.AttributeSet;
//    import javax.swing.text.BadLocationException;
//    import javax.swing.text.DefaultHighlighter;
//    import javax.swing.text.Highlighter.HighlightPainter;
//    import javax.swing.text.MutableAttributeSet;
//    import javax.swing.text.SimpleAttributeSet;
//    import javax.swing.text.StyleConstants;
//
//    import nonnull.NonNull;
//    import de.uka.iti.pseudo.gui.ProofCenter;
//    import de.uka.iti.pseudo.prettyprint.AnnotatedString;
//    import de.uka.iti.pseudo.prettyprint.AnnotatedString.Style;
//    import de.uka.iti.pseudo.prettyprint.AnnotatedString.TermElement;
//    import de.uka.iti.pseudo.prettyprint.PrettyPrint;
//    import de.uka.iti.pseudo.proof.ProofException;
//    import de.uka.iti.pseudo.proof.ProofNode;
//    import de.uka.iti.pseudo.proof.RuleApplication;
//    import de.uka.iti.pseudo.proof.SequentHistory.Annotation;
//    import de.uka.iti.pseudo.proof.SubtermSelector;
//    import de.uka.iti.pseudo.proof.TermSelector;
//    import de.uka.iti.pseudo.rule.Rule;
//    import de.uka.iti.pseudo.rule.RuleTagConstants;
//    import de.uka.iti.pseudo.term.LiteralProgramTerm;
//    import de.uka.iti.pseudo.term.Term;
//    import de.uka.iti.pseudo.util.Log;
//    import de.uka.iti.pseudo.util.NotScrollingCaret;
//    import de.uka.iti.pseudo.util.Pair;
//    import de.uka.iti.pseudo.util.TextInstantiator;
//    import de.uka.iti.pseudo.util.Util;
//    import de.uka.iti.pseudo.util.settings.Settings;
//
//    /**
//     * The Class TermComponent is used to show terms, it allows highlighting.
//     *
//     * To the user, objects of this class will appear as a single term in the
//     * sequent view.
//     */
//    public class TermComponent extends JTextPane {
//
//        private static final long serialVersionUID = -4415736579829917335L;
//
//        /**
//         * The key (to the ProofCenter property mechanism) to indicate that
//         * a term has been selected.
//         */
//        public static final String TERM_COMPONENT_SELECTED_TAG =
//                "termComponent.popup.selectedTermTag";
//
//        /**
//         * The key (to the swing property system) is used to control the drag and
//         * drop mode.
//         */
//        public static final String HIGHEST_PRIORITY_DRAG_AND_DROP =
//                "pseudo.termcomponent.autoDnD";
//
//        private static Settings S = Settings.getInstance();
//
//        /**
//         * some UI constants
//         */
//        private static final Font FONT = S.getFont("pseudo.termcomponent.font", null);
//
//        // the highlight color should be bright
//        private static final Color HIGHLIGHT_COLOR =
//            S.getColor("pseudo.termcomponent.highlightcolor", Color.ORANGE);
//
//        // the modality background should be rather unnoticed
//        private static final Color UPDATE_BACKGROUND =
//            S.getColor("pseudo.termcomponent.updatebackground", Color.CYAN.brighter().brighter());
//
//        // the modality background should be rather unnoticed
//        private static final Color PROGRAM_BACKGROUND =
//            S.getColor("pseudo.termcomponent.programbackground", Color.CYAN.brighter());
//
//        // border color needs to match background of sequent view
//        private static final Color BORDER_COLOR =
//            S.getColor("pseudo.termcomponent.bordercolor", Color.DARK_GRAY);
//
//        // variables should be noticed
//        private static final Color VARIABLE_FOREGROUND =
//            S.getColor("pseudo.termcomponent.variableforeground", Color.MAGENTA);
//
//        // assignable program variables should be noticed
//        private static final Color ASSIGNABLE_FOREGROUND =
//            S.getColor("pseudo.termcomponent.assignableforeground", Color.BLUE);
//
//        // types should be painted less noticeable
//        private static final Color TYPE_FOREGROUND =
//            S.getColor("pseudo.termcomponent.typeforeground", Color.LIGHT_GRAY);
//
//        // marking for an assumption
//        private static final Color LIGHT_MARKING_COLOR =
//            S.getColor("pseudo.termcomponent.assumptionforeground", Color.LIGHT_GRAY);
//
//        // marking for a find clause
//        private static final Color DARK_MARKING_COLOR =
//            S.getColor("pseudo.termcomponent.findforeground", Color.LIGHT_GRAY);
//
//        // empty border
//        private static final Border BORDER = BorderFactory.createCompoundBorder(
//                BorderFactory.createLineBorder(BORDER_COLOR), BorderFactory
//                        .createEmptyBorder(5, 5, 5, 5));
//
//        // the property for the bar manager to describe my popup menu
//        private static final String POPUP_PROPERTY = "termComponent.popup";
//
//        // darker and a lighter color for marking
//        private final HighlightPainter[] MARKINGS = {
//                new DefaultHighlighter.DefaultHighlightPainter(DARK_MARKING_COLOR),
//                new DefaultHighlighter.DefaultHighlightPainter(LIGHT_MARKING_COLOR) };
//
//        // remember the lighted subterms in here
//        private final List<Pair<Integer, SubtermSelector>> markedSubterms =
//                new ArrayList();
//
//        /**
//         * The term displayed
//         */
//        private final Term term;
//
//        /**
//         * the tag of the term which is currently highlighted by the mouse
//         * can be null
//         */
//        private SubtermSelector mouseSelection;
//
//        /**
//         * the position of term within its sequent
//         */
//        private final TermSelector termSelector;
//
//        /**
//         * The proofCenter to which this term belongs
//         */
//        private final ProofCenter proofCenter;
//
//        /**
//         * The annotated string containing the pretty printed term.
//         */
//        private AnnotatedString annotatedString;
//
//        /**
//         * The highlight object as returned by the highlighter.
//         * Used to highlight the mouse-selected subterm.
//         */
//        private Object theHighlight;
//
//        /**
//         * the line width calculated from the width (in characters)
//         */
//        private int lineWidth = -1;
//
//        /**
//         * the collection of highlighting objects. Used to mark find and assume
//         * instances.
//         */
//        private final List<Object> marks = new ArrayList<Object>();
//
//        /**
//         * true if the currently presented proof node to which the component belongs
//         * is open. It is used for creating the styles. Closed nodes are italic.
//         */
//        private final boolean open;
//
//        /**
//         * The history for the presented term
//         */
//        private @NonNull
//        final Annotation history;
//
//        /**
//         * pretty printing instance needed for tooltips
//         */
//        private final PrettyPrint prettyPrinter;
//
//        // not needed in the future
//        private final int verbosityLevel;
//
//        /**
//         * to handle drag and drop the original mouse position
//         * of the drag must be remembered.
//         */
//        private MouseEvent dragOrigin;
//
//        /**
//         * Instantiates a new term component.
//         *
//         * @param t
//         *                the term to display
//         * @param history
//         * @param open
//         * @param termSelector
//         *                selector object describing the position of the displayed
//         *                term in its sequent
//         */
//        public TermComponent(@NonNull Term t, Annotation history, boolean open,
//                @NonNull ProofCenter proofCenter, @NonNull TermSelector termSelector)  {
//            this.term = t;
//            this.history = history;
//            this.termSelector = termSelector;
//            this.proofCenter = proofCenter;
//            this.prettyPrinter = proofCenter.getPrettyPrinter();
//            this.verbosityLevel = (Integer)proofCenter.getProperty(ProofCenter.TREE_VERBOSITY);
//            this.annotatedString = prettyPrinter.print(t);
//            this.open = open;
//
//            assert history != null;
//            // must be toplevel
//            assert termSelector.getSubtermSelector().getDepth() == 0;
//
//            //
//            // Set display properties
//            // dnd support made manually as the lookandfeel checks
//            // whether the pointer is over selection
//            setEditable(false);
//            setFocusable(false);
//            setBorder(BORDER);
//            setCaret(new NotScrollingCaret());
//            annotatedString.appendToDocument(getDocument(), attributeFactory);
//            setTransferHandler(TermSelectionTransfer.getInstance());
//
//            DefaultHighlighter highlight = new DefaultHighlighter();
//            setHighlighter(highlight);
//            addMouseListener(new MouseAdapter() {
//                @Override
//                public void mouseExited(MouseEvent e) {
//                    TermComponent.this.mouseExited();
//                }
//                @Override
//                public void mousePressed(MouseEvent e) {
//                    TermComponent.this.mousePressed(e);
//                }
//                @Override
//                public void mouseReleased(MouseEvent e) {
//                    TermComponent.this.mouseReleased(e);
//                }
//            });
//            addMouseMotionListener(new MouseMotionAdapter() {
//                @Override
//                public void mouseMoved(MouseEvent e) {
//                    TermComponent.this.mouseMoved(e.getPoint());
//                }
//                @Override
//                public void mouseDragged(MouseEvent e) {
//                    TermComponent.this.mouseDragged(e);
//                }
//            });
//            addPropertyChangeListener("dropLocation", new PropertyChangeListener() {
//                @Override
//                public void propertyChange(PropertyChangeEvent evt) {
//                    DropLocation loc = (DropLocation) evt.getNewValue();
//                    if(loc != null) {
//                        TermComponent.this.mouseMoved(loc.getDropPoint());
//                    } else {
//                        TermComponent.this.mouseExited();
//                    }
//                }
//            });
//            addComponentListener(new ComponentAdapter() {
//                @Override
//                public void componentResized(ComponentEvent e) {
//                    int newLineWidth = computeLineWidth();
//                    if(newLineWidth != lineWidth) {
//                        annotatedString = prettyPrinter.print(term, newLineWidth);
//                        setText("");
//                        annotatedString.appendToDocument(getDocument(), attributeFactory);
//                        lineWidth = newLineWidth;
//                        for (Pair<Integer, SubtermSelector> p : markedSubterms) {
//                            addMarkSubterm(p.snd(), p.fst());
//                        }
//                    }
//                }
//            });
//
//            try {
//                theHighlight = highlight.addHighlight(0, 0,
//                        new DefaultHighlighter.DefaultHighlightPainter(
//                                HIGHLIGHT_COLOR));
//            } catch (BadLocationException e) {
//                // may not happen even if document is empty
//                throw new Error(e);
//            }
//
//            //
//            // add popup
//            try {
//                JPopupMenu popupMenu = proofCenter.getBarManager().makePopup(POPUP_PROPERTY);
//                setComponentPopupMenu(popupMenu);
//    //            popupMenu.addPopupMenuListener(popupMenuListener);
//            } catch (IOException ex) {
//                Log.log(Log.DEBUG, "Disabling popup menu in term component");
//                Log.stacktrace(ex);
//            }
//        }
//
//
//        /*
//         * store created attribute sets in a cache.
//         */
//        private static Map<Set<Style>, AttributeSet> attributeCache =
//            new HashMap<Set<Style>, AttributeSet>();
//
//        /*
//         * This is used by AnnotatedStringWithStyles to construct styles.
//         */
//        private final AnnotatedString.AttributeSetFactory attributeFactory =
//            new AnnotatedString.AttributeSetFactory() {
//            @Override
//            public AttributeSet makeStyle(Set<Style> styles) {
//
//                if(!open) {
//                    styles.add(Style.CLOSED);
//                }
//
//                AttributeSet cached = attributeCache.get(styles);
//
//                if (cached == null) {
//
//                    MutableAttributeSet retval = new SimpleAttributeSet();
//                    if(FONT != null) {
//                        StyleConstants.setFontFamily(retval, FONT.getFamily());
//                        StyleConstants.setFontSize(retval, FONT.getSize());
//                    }
//
//                    for (Style style : styles) {
//                        switch(style) {
//                        case PROGRAM:
//                            StyleConstants.setBackground(retval, PROGRAM_BACKGROUND);
//                            break;
//                        case UPDATE:
//                            StyleConstants.setBackground(retval, UPDATE_BACKGROUND);
//                            break;
//                        case KEYWORD:
//                            StyleConstants.setBold(retval, true);
//                            break;
//                        case VARIABLE:
//                            StyleConstants.setForeground(retval, VARIABLE_FOREGROUND);
//                            break;
//                        case TYPE:
//                            StyleConstants.setForeground(retval, TYPE_FOREGROUND);
//                            break;
//                        case ASSIGNABLE:
//                            StyleConstants.setForeground(retval, ASSIGNABLE_FOREGROUND);
//                            break;
//                        case CLOSED:
//                            StyleConstants.setItalic(retval, true);
//                            break;
//                        }
//                    }
//
//                    attributeCache.put(styles, retval);
//                    cached = retval;
//                }
//
//                return cached;
//            }
//
//        };
//
//
//        /*
//         * Mouse exited the component: remove highlighting
//         */
//        private void mouseExited() {
//            try {
//                getHighlighter().changeHighlight(theHighlight, 0, 0);
//                mouseSelection = null;
//            } catch (BadLocationException ex) {
//                // this shant happen
//                throw new Error(ex);
//            }
//        }
//
//        protected void mousePressed(MouseEvent e) {
//            if(SwingUtilities.isLeftMouseButton(e)) {
//                dragOrigin = e;
//            }
//        }
//
//        protected void mouseReleased(MouseEvent e) {
//            dragOrigin = null;
//        }
//
//        /*
//         * Mouse moved: move the highlighting
//         */
//        protected void mouseMoved(Point p) {
//            Log.enter(p);
//            int index = viewToModel(p);
//            try {
//                if (index >= 0 && index < annotatedString.length()) {
//                    TermElement element = annotatedString.getTermElementAt(index);
//                    int begin = element.getBegin();
//                    int end = element.getEnd();
//                    getHighlighter().changeHighlight(theHighlight, begin, end);
//
//                    mouseSelection = annotatedString.getTermElementAt(index).getSubtermSelector();
//                    setToolTipText(makeTermToolTip(mouseSelection));
//
//                    proofCenter.firePropertyChange(TERM_COMPONENT_SELECTED_TAG, TermComponent.this);
//
//                    if (null != mouseSelection) {
//                        Log.log(Log.VERBOSE, mouseSelection);
//                    }
//                } else {
//                    getHighlighter().changeHighlight(theHighlight, 0, 0);
//                    mouseSelection = null;
//                }
//            } catch (BadLocationException ex) {
//                ex.printStackTrace();
//            }
//        }
//
//        protected void mouseDragged(MouseEvent e) {
//            if(dragOrigin != null) {
//                getTransferHandler().exportAsDrag(this, dragOrigin, TransferHandler.COPY);
//            }
//        }
//
//        /**
//         * Create the tool tip text: original text of the term with the type at the
//         * end. The string is shortened to 128 characters if necessary
//         */
//        private String makeTermToolTip(SubtermSelector termTag) {
//            Term t;
//            try {
//                t = termTag.selectSubterm(term);
//            } catch (ProofException e) {
//                Log.log(Log.WARNING, "Cannot create tooltip for " + termTag);
//                Log.stacktrace(Log.WARNING, e);
//                return "";
//            }
//
//            String rval = t.toString() + " as " + t.getType();
//            if (rval.length() > 128) {
//                rval = rval.substring(0, 125) + "...";
//            }
//            return rval;
//        }
//
//        /**
//         * calculate the text to display in "information for this formula" for a
//         * term. This is a rather complex document:
//         *
//         * <ol>
//         * <li>the type
//         * <li>For programs, print the current statement
//         * <li>The history, at least the first 60 elements
//         * </ol>
//         *
//         * @param termTag
//         *            tag to print info on
//         *
//         */
//        public String makeFormatedTermHistory(SubtermSelector termTag) {
//            Term locterm;
//            try {
//                locterm = termTag.selectSubterm(term);
//            } catch (ProofException e) {
//                Log.log(Log.WARNING, "Cannot create history for " + termTag);
//                Log.stacktrace(Log.WARNING, e);
//                return "";
//            }
//
//            StringBuilder sb = new StringBuilder();
//
//            //
//            // type
//            sb.append("<html><dl><dt>Type:</dt><dd>").append(locterm.getType()).append("</dd>\n");
//
//            //
//            // statement
//            if (locterm instanceof LiteralProgramTerm) {
//                LiteralProgramTerm prog = (LiteralProgramTerm) locterm;
//                String stm = prettyPrinter.print(prog.getStatement()).toString();
//                sb.append("<dt>Statement:</dt><dd>").append(stm).append("</dd>\n");
//            }
//
//            //
//            // history
//            Annotation h = history;
//            sb.append("<dt>History:</dt><dd><ol>");
//            int len = 0;
//            while (h != null && len < 60) {
//                ProofNode creatingProofNode = h.getCreatingProofNode();
//                if (creatingProofNode == null || shouldShow(creatingProofNode)) {
//                    String text = h.getText();
//
//                    if (creatingProofNode != null) {
//                        text = instantiateString(creatingProofNode.getAppliedRuleApp(), text);
//
//                        sb.append("<li>Node ").append(creatingProofNode.getNumber()).append(": ");
//                    }
//                    sb.append(text);
//                    sb.append("</li>\n");
//                    len++;
//                }
//                h = h.getParentAnnotation();
//            }
//            sb.append("</ol>\n");
//            if (len == 60) {
//                sb.append("... truncated history");
//            }
//
//            sb.append("</dl>");
//
//            // System.out.println(sb);
//            return sb.toString();
//        }
//
//        /**
//         * check whether verbosity makes us show this node:
//         * - verbosity of node <= set verbosity
//         *
//         * @see ProofComponentModel#shouldShow(ProofNode)
//         */
//        private boolean shouldShow(ProofNode node) {
//            RuleApplication ruleApp = node.getAppliedRuleApp();
//
//            if(ruleApp == null) {
//                return true;
//            }
//
//            // not here
//            // if(node.getChildren() == null)
//            //     return true;
//
//            Rule rule = ruleApp.getRule();
//            String string = rule.getProperty(RuleTagConstants.KEY_VERBOSITY);
//            int value = 0;
//            try {
//                if(string != null) {
//                    value = Util.parseUnsignedInt(string);
//                }
//            } catch (NumberFormatException e) {
//                return true;
//            }
//
//            return value <= verbosityLevel;
//        }
//
//        /*
//         * instantiate the schema variables in a string.
//         * @see ProofComponentModel
//         *
//         */
//        private String instantiateString(RuleApplication ruleApp, String string) {
//            TextInstantiator textInst = new TextInstantiator(ruleApp);
//            return textInst.replaceInString(string, prettyPrinter);
//        }
//
//        /**
//         * Gets the termselector for a subterm at a certain point in the component
//         *
//         * @param point
//         *            the point within the component
//         *
//         * @return the selector for the subterm at this point or null if there is none
//         */
//        public TermSelector getTermAt(Point point) {
//            int charIndex = viewToModel(point);
//            SubtermSelector sel =
//                    annotatedString.getTermElementAt(charIndex).getSubtermSelector();
//            if(sel == null) {
//                return null;
//            }
//
//            return new TermSelector(termSelector, sel);
//        }
//
//        // stolen from KeY
//        @Override
//        public int viewToModel(Point p) {
//            String seqText = getText();
//
//            // bugfix for empty strings
//            if (seqText.length() == 0) {
//                return 0;
//            }
//
//            int cursorPosition = super.viewToModel(p);
//
//            cursorPosition -= (cursorPosition > 0 ? 1 : 0);
//
//            cursorPosition = (cursorPosition >= seqText.length() ? seqText.length() - 1
//                    : cursorPosition);
//            cursorPosition = (cursorPosition >= 0 ? cursorPosition : 0);
//
//            int previousCharacterWidth = getFontMetrics(getFont()).charWidth(
//                    seqText.charAt(cursorPosition));
//
//            int characterIndex = super.viewToModel(new Point((int) p.getX()
//                    - (previousCharacterWidth / 2), (int) p.getY()));
//
//            characterIndex = Math.max(0, characterIndex);
//
//            return characterIndex;
//        }
//
//        public void markSubterm(SubtermSelector selector, int type) {
//            if (type < 0 || type >= MARKINGS.length) {
//                throw new IndexOutOfBoundsException();
//            }
//
//            markedSubterms.add(Pair.make(type, selector));
//            addMarkSubterm(selector, type);
//        }
//
//        private void addMarkSubterm(SubtermSelector selector, int type) {
//
//            int begin = -1;
//            int end = -1;
//            if(selector.getDepth() == 0) {
//                // toplevel term --> implicitly stored
//                begin = 0;
//                end = getDocument().getLength();
//            } else {
//                for(TermElement block : annotatedString.getAllTermElements()) {
//                    SubtermSelector sel = block.getSubtermSelector();
//                    if(sel.equals(selector)) {
//                        begin = block.getBegin();
//                        end = block.getEnd();
//                        break;
//                    }
//                }
//            }
//
//            if(begin == -1) {
//                Log.log(Log.WARNING, "cannot mark subterm " + selector + " in " + annotatedString);
//                return;
//            }
//
//            try {
//                Object mark = getHighlighter().addHighlight(begin, end, MARKINGS[type]);
//                marks.add(mark);
//            } catch (BadLocationException e) {
//                throw new Error(e);
//            }
//        }
//
//        /**
//         * removes all highlights
//         */
//        void clearMarks() {
//            for (Object highlight : marks) {
//                getHighlighter().removeHighlight(highlight);
//            }
//            marks.clear();
//            markedSubterms.clear();
//        }
//
//        /**
//         * used by drag and drop to create a transferable version, i.e. a string, of
//         * the selected formula
//         */
//        public Transferable createTransferable() {
//            if(mouseSelection == null) {
//                return null;
//            }
//
//            try {
//                return new TermSelectionTransferable(this,
//                        new TermSelector(termSelector, mouseSelection),
//                        mouseSelection.selectSubterm(term).toString(true));
//            } catch (ProofException e) {
//                throw new Error(e);
//            }
//        }
//
//        /**
//         * basic getter
//         */
//        public SubtermSelector getMouseSelection() {
//            return mouseSelection;
//        }
//
//        /**
//         * returns the ProofCenter it belongs to
//         */
//        final ProofCenter getProofCenter() {
//            return proofCenter;
//        }
//
//        /**
//         * @return a list of rules which can be applied to the selected term
//         * @throws ProofException
//         *             see {@link ProofCenter#getApplicableRules(TermSelector)}
//         */
//        List<RuleApplication> getApplicableRules() throws ProofException {
//            if (null == mouseSelection) {
//                return new ArrayList<RuleApplication>(0);
//            } else {
//                return proofCenter.getApplicableRules(new TermSelector(termSelector, mouseSelection));
//            }
//        }
//
//        public Term getTerm() {
//            return term;
//        }
//
//        /**
//         * Computes the line width.
//         *
//         * Uses the dimensions and fontmetrics. Needs a proportional font.
//         * (taken from KeY!)
//         *
//         * @return the number of characters in one line
//         */
//        private int computeLineWidth() {
//            // assumes we have a uniform font width
//            int maxChars = getSize().width /
//                    getFontMetrics(getFont()).charWidth('W');
//
//            if (maxChars > 1) {
//                maxChars -= 1;
//            }
//
//            return maxChars;
//        }
//
//        /**
//         * Gets the history for the displayed term.
//         *
//         * @return n non-<code>null</code> history object.
//         */
//        public @NonNull Annotation getHistory() {
//            return history;
//        }
//
//    }
