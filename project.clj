(defproject lti-model "0.1.0-SNAPSHOT"
  :description "FIXME: write description"
  :url "http://example.com/FIXME"
  :license {:name "Eclipse Public License"
            :url "http://www.eclipse.org/legal/epl-v10.html"}
  ; 2gb stack size
  :jvm-opts ["-Xss1g"]
  :dependencies [[org.clojure/clojure "1.9.0"]
                 [dorothy "0.0.7"]
                 [hiccup "1.0.5"]])
