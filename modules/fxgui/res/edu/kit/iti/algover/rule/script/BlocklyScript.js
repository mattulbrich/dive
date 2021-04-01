var errorNode = null

function highlight(elemid) {
    const elem = document.getElementById(elemid);
    if (elem === null) {
        return;
    }
    elem.style.borderTopWidth = "15px";
    elem.style.borderTopColor = "c80000";
}

function resetError() {
    errorNode == null;
}

function setError(elemid) {
    const elem = document.getElementById(elemid);
    errorNode = elem
    if (elem === null) {
        return;
    }

    errorNode.style.border = "5px solid red";

}

function unhighlight(elemid) {
    const elem = document.getElementById(elemid);
    if (elem === null) {
        return;
    }
    elem.style.borderTopWidth = "";
    elem.style.borderTopColor = "";

    if (elem == errorNode) {
        errorNode.style.border = "5px solid red";
    }

}

function hide(elemid) {
    const elem = document.getElementById(elemid);
    if (elem === null) {
        return;
    }
    elem.style.display = "none";

}

function setStyle(elemid, stylename) {
    const elem = document.getElementById(elemid);
    elem.className = stylename;

}