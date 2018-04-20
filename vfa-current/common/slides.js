/* Presentation mode for SF HTML
 *
 * This file implements simple slide functionality for the SF HTML
 * files. When loaded in a page, it will tag some of the page elements
 * as slide boundaries, giving each an id of the form
 * "#slide-XX". Pressing left or right should trigger "slide mode",
 * focusing the screen on the current slide, and then navigate between
 * slides. Pressing escape brings the page back to normal. */

/* Which DOM elements to mark as slide boundaries */
var slideSelector = 'h1.libtitle, h1.section, h2.section, h3.section, .quiz';

/* Whether or not we are in slide mode */
var slideMode = false;

/* Navigates between slides, using the current location hash to find
 * the next slide to go to */
function slideNavigate(direction) {

    function slideNumber(s) {
        if (!s) return null;
        var match = s.match(/slide-(.*)/);
        if (match && match.length != 0) {
            return parseInt(match[1]);
        }
        return null;
    }

    var curSlide = slideNumber(location.hash);
    var lastSlide = slideNumber($('.slide').last().attr('id'));
    var nextSlide;

    /* We change the id of each slide element when the page loads, and
     * then switch between slides based on the current hash. This is
     * not entirely optimal, and can probably be made better.
     * http://www.appelsiini.net/projects/viewport seems to be a nice choice.
     */

    if (direction == 'left') {
        if (curSlide != null) {
            if (curSlide > 0) {
                nextSlide = curSlide - 1;
            } else {
                nextSlide = lastSlide;
            }
        } else {
            nextSlide = 0;
        }
    } else if (direction == 'right') {
        if (curSlide != null && curSlide < lastSlide) {
            nextSlide = curSlide + 1;
        } else {
            nextSlide = 0;
        }
    }

    location.hash = '#slide-' + nextSlide;

    return false;
};

/* Force the browser to scroll back to the hash location */
function refreshHash() {
    var t = location.hash;
    location.hash = '';
    location.hash = t;
}

/* Activate slide mode. Inserts the right amount of spacing between
 * slide boundaries, ensuring that only one slide appears on the
 * screen at a time */
function slideActivate() {
    $('.slide').each(function (i, elt) {
        if (i > 0) $(elt).css('margin-top', $(window).height());
        $(elt).css('height', '20px');
    });
    $('#main').css('padding-bottom', $(window).height());
    slideMode = true;
    if (location.hash) {
        refreshHash();
    } else {
        location.hash = '#slide-0';
    }
}

/* Deactivate slide mode. Removes the extra spacing between slides */
function slideDeactivate() {
    $('.slide').each(function (i, elt) {
        $(elt).css('margin-top', 0);
        $(elt).css('height', 0);
    });
    $('#main').css('padding-bottom', 0);
    refreshHash();
    slideMode = false;
}

/* Set up appropriate input handlers */
$(document).keydown(function (event) {
    if (slideMode) {
        if (event.keyCode == 37) {
            slideNavigate('left');
        } else if (event.keyCode == 39) {
            slideNavigate('right');
        } else if (event.keyCode == 27) { // escape
            slideDeactivate();
        } else return true;
    } else {
        if (event.keyCode == 37 || event.keyCode == 39) {
            slideActivate();
            return false;
        } else {
            return true;
        }
    }
});

/* Find slide boundaries and tag them */
$(document).ready(function () {
    $(slideSelector).each(function (i, elt) {
        var mark = '<div class="slide" id="slide-' + i + '" />';
        $(mark).insertBefore($(elt));
    });
    if (location.hash) {
        slideActivate();
    }
});
