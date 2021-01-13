
function highlight(elemid) {
    const elem = document.getElementById(elemid);
    if (elem === null) {
        return;
    }
    elem.style.borderTopWidth = "15px";
    elem.style.borderTopColor = "c80000";
}

function unhighlight(elemid) {
    const elem = document.getElementById(elemid);
    if (elem === null) {
        return;
    }
    elem.style.borderTopWidth = "";
    elem.style.borderTopColor = "";
}

function hide(elemid) {
    const elem = document.getElementById(elemid);
    elem.style.display = "none";

}

function selectAfterLeaf(elemid) {
    const elem = document.getElementById(elemid);
    elem.className = "afterLeafSelected";
}

function setOpenEnd(elemid) {
    document.getElementById(elemid).setAttribute("class", "opengoal");
}

function setClosed(elemid) {
    document.getElementById(elemid).setAttribute("class", "closed");
}