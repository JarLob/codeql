---
category: query
---
* The `actions/untrusted-checkout-toctou/critical` query now uses the untrusted checkout as its primary alert location. Multiple downstream execution paths from the same checkout are retained as code-flow variants of one alert instead of producing separate alerts.