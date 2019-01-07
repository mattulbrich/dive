package edu.kit.iti.algover.rule.script;

import edu.kit.iti.algover.script.ast.Position;
import javafx.beans.binding.BooleanBinding;
import javafx.beans.property.*;

/**
 * Properties for the annotations for the scriptview gutter
 * @author A. Weigl (PSDBG)
 */
public class GutterAnnotation {

    public void setLineNumber(int lineNumber) {
        this.lineNumber = lineNumber;
    }

    private int lineNumber;

    public int getLineNumber() {
        return lineNumber;
    }

    private StringProperty text = new SimpleStringProperty();

    private SimpleBooleanProperty insertMarker = new SimpleBooleanProperty(false, "Marker for insertion");


    public boolean isInsertMarker() {
        return insertMarker.get();
    }

    public SimpleBooleanProperty insertMarkerProperty() {
        return insertMarker;
    }

    public void setInsertMarker(boolean insertMarker) {
        this.insertMarker.set(insertMarker);
    }


        public String getText() {
            return text.get();
        }

        public void setText(String text) {
            this.text.set(text);
        }

        public StringProperty textProperty() {
            return text;
        }

    // private SimpleBooleanProperty breakpoint = new SimpleBooleanProperty();

    // private StringProperty breakpointCondition = new SimpleStringProperty();

    // private BooleanBinding conditional = breakpointCondition.isNotNull().and(breakpointCondition.isNotEmpty());


    //for now specifically for skipped saved commands
//        private SimpleBooleanProperty alert = new SimpleBooleanProperty();

/*        public boolean isAlert() {
            return alert.get();
        }

        public void setAlert(boolean alert) {
            this.alert.set(alert);
        }

        public SimpleBooleanProperty alertProperty() {
            return alert;
        }
*/




/*
        public boolean isBreakpoint() {
            return breakpoint.get();
        }

        public void setBreakpoint(boolean breakpoint) {
            this.breakpoint.set(breakpoint);
        }

        public SimpleBooleanProperty breakpointProperty() {
            return breakpoint;
        }

        public String getBreakpointCondition() {
            return breakpointCondition.get();
        }

        public void setBreakpointCondition(String breakpointCondition) {
            this.breakpointCondition.set(breakpointCondition);
        }

        public StringProperty breakpointConditionProperty() {
            return breakpointCondition;
        }

        public Boolean getConditional() {
            return conditional.get();
        }

        public BooleanBinding conditionalProperty() {
            return conditional;
        }

*/
}
