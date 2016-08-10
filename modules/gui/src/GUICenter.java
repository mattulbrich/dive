import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeListenerProxy;
import java.beans.PropertyChangeSupport;

/**
 * SpiderPattern class
 * Manages ditsribution of data to show in GUI components
 *
 * All relevant listeners should register here
 *
 *
 * Created by sarah on 8/3/16.
 */


public class GUICenter {
     /**
     * Boolean property that is set, if a project is completely loaded and the project object is returned
     *
     */
    public static final String PROJECT_LOADED = "project_loaded";

    /**
     * Boolean property that is set, if the dafny source has been edited
     *
     */
    public static final String DAFNY_SOURCE_CHANGED = "dafny_source_changed";

    public static  final String LOGICAL_VIEW_CHANGED = "logical_view_changed";

    public static final String PVC_STATUS_CHANGED = "pvc_status_changed";

    public static final String PORERTY_CHANGED = "property_changed";



}
