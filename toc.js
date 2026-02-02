// Populate the sidebar
//
// This is a script, and not included directly in the page, to control the total size of the book.
// The TOC contains an entry for each page, so if each page includes a copy of the TOC,
// the total size of the page becomes O(n**2).
class MDBookSidebarScrollbox extends HTMLElement {
    constructor() {
        super();
    }
    connectedCallback() {
        this.innerHTML = '<ol class="chapter"><li class="chapter-item expanded affix "><li class="part-title">What is act?</li><li class="chapter-item expanded "><a href="introduction.html"><strong aria-hidden="true">1.</strong> Introduction</a></li><li class="chapter-item expanded "><a href="installation.html"><strong aria-hidden="true">2.</strong> Getting Started and Installation</a></li><li class="chapter-item expanded "><a href="running_ex.html"><strong aria-hidden="true">3.</strong> A First Look: ERC20 as Running Example</a></li><li class="chapter-item expanded affix "><li class="part-title">Specification Language act</li><li class="chapter-item expanded "><a href="syntax.html"><strong aria-hidden="true">4.</strong> Syntax Overview</a></li><li class="chapter-item expanded "><a href="store_type.html"><strong aria-hidden="true">5.</strong> Storage, Typing and Expressions</a></li><li class="chapter-item expanded "><a href="constructors.html"><strong aria-hidden="true">6.</strong> Constructors and Initial State</a></li><li class="chapter-item expanded "><a href="transitions.html"><strong aria-hidden="true">7.</strong> Transitions and Storage Updates</a></li><li class="chapter-item expanded "><a href="how_to.html"><strong aria-hidden="true">8.</strong> How to Write Your Own Spec</a></li><li class="chapter-item expanded affix "><li class="part-title">Type-Checking and No-Aliasing</li><li class="chapter-item expanded "><a href="type_checking.html"><strong aria-hidden="true">9.</strong> Type-Checking</a></li><li class="chapter-item expanded "><a href="aliasing.html"><strong aria-hidden="true">10.</strong> Aliasing and Unique Ownership</a></li><li class="chapter-item expanded affix "><li class="part-title">Verification with act</li><li class="chapter-item expanded "><a href="equiv.html"><strong aria-hidden="true">11.</strong> hevm backend: Equivalence to EVM bytecode</a></li><li class="chapter-item expanded "><a href="rocq.html"><strong aria-hidden="true">12.</strong> Rocq backend</a></li></ol>';
        // Set the current, active page, and reveal it if it's hidden
        let current_page = document.location.href.toString().split("#")[0];
        if (current_page.endsWith("/")) {
            current_page += "index.html";
        }
        var links = Array.prototype.slice.call(this.querySelectorAll("a"));
        var l = links.length;
        for (var i = 0; i < l; ++i) {
            var link = links[i];
            var href = link.getAttribute("href");
            if (href && !href.startsWith("#") && !/^(?:[a-z+]+:)?\/\//.test(href)) {
                link.href = path_to_root + href;
            }
            // The "index" page is supposed to alias the first chapter in the book.
            if (link.href === current_page || (i === 0 && path_to_root === "" && current_page.endsWith("/index.html"))) {
                link.classList.add("active");
                var parent = link.parentElement;
                if (parent && parent.classList.contains("chapter-item")) {
                    parent.classList.add("expanded");
                }
                while (parent) {
                    if (parent.tagName === "LI" && parent.previousElementSibling) {
                        if (parent.previousElementSibling.classList.contains("chapter-item")) {
                            parent.previousElementSibling.classList.add("expanded");
                        }
                    }
                    parent = parent.parentElement;
                }
            }
        }
        // Track and set sidebar scroll position
        this.addEventListener('click', function(e) {
            if (e.target.tagName === 'A') {
                sessionStorage.setItem('sidebar-scroll', this.scrollTop);
            }
        }, { passive: true });
        var sidebarScrollTop = sessionStorage.getItem('sidebar-scroll');
        sessionStorage.removeItem('sidebar-scroll');
        if (sidebarScrollTop) {
            // preserve sidebar scroll position when navigating via links within sidebar
            this.scrollTop = sidebarScrollTop;
        } else {
            // scroll sidebar to current active section when navigating via "next/previous chapter" buttons
            var activeSection = document.querySelector('#sidebar .active');
            if (activeSection) {
                activeSection.scrollIntoView({ block: 'center' });
            }
        }
        // Toggle buttons
        var sidebarAnchorToggles = document.querySelectorAll('#sidebar a.toggle');
        function toggleSection(ev) {
            ev.currentTarget.parentElement.classList.toggle('expanded');
        }
        Array.from(sidebarAnchorToggles).forEach(function (el) {
            el.addEventListener('click', toggleSection);
        });
    }
}
window.customElements.define("mdbook-sidebar-scrollbox", MDBookSidebarScrollbox);
