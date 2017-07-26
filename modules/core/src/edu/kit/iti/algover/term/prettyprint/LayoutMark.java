/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.prettyprint;

import edu.kit.iti.algover.term.prettyprint.AnnotatedString.Style;

interface LayoutMark {
    public void handle(AnnotatedString as);

    class BeginTerm implements LayoutMark {
        private final int subtermno;

        public BeginTerm(int subtermno) {
            this.subtermno = subtermno;
        }

        @Override
        public void handle(AnnotatedString as) {
            as.handleBeginTerm(subtermno);
        }
    }

    class EndTerm implements LayoutMark {
        @Override
        public void handle(AnnotatedString as) {
            as.handleEndTerm();
        }
    }

    class PushStyle implements LayoutMark {
        private final Style style;

        public PushStyle(Style style) {
            this.style = style;
        }

        @Override
        public void handle(AnnotatedString as) {
            as.handlePushStyle(style);
        }
    }

    class PopStyle implements LayoutMark {
        @Override
        public void handle(AnnotatedString as) {
            as.handlePopStyle();
        }
    }
}