// Only fail in CI
val isCI = System.getenv("CI") == "true"

plugins {
    application
    java
    id("checkstyle")
    id("pmd")
    id("com.github.spotbugs") version "6.1.9"
}

repositories {
    mavenCentral()
}

dependencies {
    implementation("com.google.guava:guava:31.0.1-jre")
    testImplementation("org.junit.jupiter:junit-jupiter-api:5.8.2")
    testImplementation("org.junit.jupiter:junit-jupiter-engine:5.8.2")
}

tasks.test {
    useJUnitPlatform()
}
tasks.register("buildSafe") {
    group = "build"
    description = "Builds the project without running static analysis"
    dependsOn("compileJava", "testClasses", "jar", "test") // Everything but check
}

java {
    toolchain {
        languageVersion.set(JavaLanguageVersion.of(17))
    }
}

application {
    mainClass.set("org.example.Pentago")
}

pmd {
    toolVersion = "6.55.0"
    ruleSets = listOf("category/java/bestpractices.xml", "category/java/errorprone.xml")
    isConsoleOutput = true
}

spotbugs {
    toolVersion = "4.9.3"
}

// === Checkstyle ===
checkstyle {
    toolVersion = "10.2"
    val configFile = file("config/checkstyle/checkstyle.xml")
    if (!configFile.exists()) {
        throw GradleException("Checkstyle config not found: $configFile")
    }
    config = resources.text.fromFile(configFile)
    isShowViolations = true
}

// === Safe Exec Task ===
tasks.register("bEx") {
    group = "build"
    description = "Runs build and test ignoring static analysis failures"
    dependsOn("build", "test")
    outputs.upToDateWhen { false } // Force task to always run
}

tasks.withType<org.gradle.api.plugins.quality.Pmd>().configureEach {
    ignoreFailures = !isCI  // only fail in CI
}

tasks.withType<Checkstyle>().configureEach {
    ignoreFailures = !isCI  // only fail in CI
}

tasks.withType<com.github.spotbugs.snom.SpotBugsTask>().configureEach {
    ignoreFailures = !isCI  // only fail in CI
}
