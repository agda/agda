var highlight = function (on) {
  return function () {
    var links = document.getElementsByTagName('a');
    for (var i = 0; i < links.length; i++) {
      var that = links[i];

      if (this.href != that.href) {
        continue;
      }

      if (on) {
        that.classList.add("hover-highlight");
      } else {
        that.classList.remove("hover-highlight");
      }
    }
  }
};

window.onload = function () {
  var links = document.getElementsByTagName('a');
  for (var i = 0; i < links.length; i++) {
    var link = links[i];
    if (!link.hasAttribute("href")) continue;
    link.onmouseover = highlight(true);
    link.onmouseout = highlight(false);
  }
};